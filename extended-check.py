import binascii
import collections
import hashlib
import multiprocessing.pool
import os
import re
import sys
import struct
import zlib

def normalize_path(path):
    while path.startswith('./'):
        path = path[2:]

    path = re.sub(r'/(\./)+', '/', path)
    path = re.sub(r'(^|/)[^/]+/\.\.(/|$)', r'\1\2', path)
    path = re.sub(r'/+', '/', path)
    
    while path.endswith('/'):
        path = path[:-1]

    return path

class CRC32Hasher(object):
    def __init__(self):
        self.crc = zlib.crc32('')

    def update(self, chunk):
        self.crc = zlib.crc32(chunk, self.crc)

    def digest(self):
        return struct.pack('>I', self.crc & 0xffffffff)

def run_sums(fh, hashers):
    while True:
        chunk = fh.read(1024*1024)
        if len(chunk) == 0:
            break

        for h in hashers:
            h.update(chunk)

def make_hashers(kinds):
    def make_hasher(kind):
        if kind == 'crc32':
            return CRC32Hasher()
        else:
            return hashlib.new(kind)
    return map(make_hasher, kinds)

def get_hashes(filename, kinds):
    with open(filename, 'rb', 0) as fh:
        hashers = make_hashers(kinds)
        run_sums(fh, hashers)
        return dict(zip(kinds, map(lambda h: h.digest(), hashers)))

class VerificationData(object):
    def __init__(self):
        self.found_names = set()
        self.skip_verify = set()
        self.hashes = collections.defaultdict(dict)
        self.other_data = collections.defaultdict(dict)

    def add_par2(self, file_path):
        self.found_names.add(file_path)
        self.skip_verify.add(file_path)

        base = os.path.dirname(file_path)

        with open(file_path, 'r') as fh:
            while True:
                buf = fh.read(4)
                if len(buf) == 0:
                    break

                if buf != 'PAR2':
                    continue

                buf = fh.read(4)
                if buf != '\x00PKT':
                    continue

                packet_length = struct.unpack('<Q', fh.read(8))[0]
                if packet_length % 4 != 0 or packet_length < 64:
                    # no packet has these lengths
                    continue

                packet_hash = fh.read(16)
                packet_rsetid = fh.read(16)
                packet_type = fh.read(16)
                if packet_type != 'PAR 2.0\x00FileDesc':
                    # skip this packet
                    fh.seek(packet_length-64, 1)
                    continue

                packet_data = fh.read(packet_length - 64)
                if hashlib.md5(packet_rsetid + packet_type + packet_data).digest() != packet_hash:
                    # corrupt packet
                    continue

                # packet_data contains:
                # 0-15 file id
                # 16-31 md5 hash of entire file
                # 32-47 md5 hash of first 16KiB
                # 48-55 byte length of file
                # 56-end filename, null padded

                file_md5 = packet_data[16:32]
                file_length = struct.unpack('<Q', packet_data[48:56])[0]
                file_name = packet_data[56:]
                while file_name.endswith('\x00'):
                    file_name = file_name[:-1]

                path = normalize_path(os.path.join(base, file_name))

                self.hashes[path]['md5'] = file_md5
                self.other_data[path]['length'] = file_length

    def add_sfv(self, file_path):
        self.found_names.add(file_path)
        self.skip_verify.add(file_path)

        base = os.path.dirname(file_path)

        sizes = dict()
        sizes_are_mod_2_32 = False

        with open(file_path, 'r') as fh:
            for line in fh:
                if line.startswith('; Generated by cksfv'):
                    sizes_are_mod_2_32 = True
                    continue

                res = re.match(r'^;\s+(\d+)\s+\d\d?:\d\d?\.\d\d?\s+\d\d\d\d-\d\d-\d\d\s+(.+?)\s*$', line)
                if res:
                    sizes[res.group(2)] = long(res.group(1))
                    continue

                res = re.match(r'^;\s+(.+?)\s+([\d,]+)\s+\d\d?:\d\d?:\d\d?\s+\d\d?/\d\d?/\d\d\d\d\s*$', line)
                if res:
                    sizes[res.group(1)] = long(res.group(2).replace(',', ''))
                    continue

                res = re.match(r'^([^;].*?)\s+([a-fA-F0-9]{8})\s*$', line)
                if res:
                    windows_filename = res.group(1)
                    crc32 = res.group(2)

                    local_filename = windows_filename.replace('\\', '/')
                    path = normalize_path(os.path.join(base, local_filename))

                    self.hashes[path]['crc32'] = binascii.a2b_hex(crc32)
                    if windows_filename in sizes:
                        if sizes_are_mod_2_32:
                            self.other_data[path]['length_mod_2e32'] = sizes[windows_filename]
                        else:
                            self.other_data[path]['length'] = sizes[windows_filename]

    def add_md5sum(self, file_path):
        self.found_names.add(file_path)
        self.skip_verify.add(file_path)

        base = os.path.dirname(file_path)

        with open(file_path, 'r') as fh:
            for line in fh:
                res = re.match(r'^([a-fA-F0-9]{32})\s[*\s](.+?)\s*$', line)
                if res:
                    path = normalize_path(os.path.join(base, res.group(2)))
                    db['hashes'][path]['md5'] = binascii.a2b_hex(res.group(1))

    def add_shasum(self, file_path):
        self.found_names.add(file_path)
        self.skip_verify.add(file_path)

        base = os.path.dirname(file_path)

        with open(file_path, 'r') as fh:
            for line in fh:
                res = re.match(r'^([a-fA-F0-9]{40,128})\s[*\s](.+?)\s*$', line)
                if res:
                    path = normalize_path(os.path.join(base, res.group(2)))
                    hash = binascii.a2b_hex(res.group(1))
                    if len(res.group(1)) == 40:
                        self.hashes[path]['sha1'] = hash
                    elif len(res.group(1)) == 64:
                        self.hashes[path]['sha256'] = hash
                    elif len(res.group(1)) == 128:
                        self.hashes[path]['sha512'] = hash

    def add_tree(self, path, verbose=False):
        crc32_regexes = [
            re.compile('.+\[([a-fA-F0-9]{8})\]'),
            re.compile('.+\{([a-fA-F0-9]{8})\}'),
            re.compile('.+\(([a-fA-F0-9]{8})\)'),
            re.compile('.+[^a-zA-Z0-9]([a-fA-F0-9]{8})\.[^.]{3,4}$'),
        ]

        for root, dirs, files in os.walk(path):
            for i in range(len(dirs)):
                if i >= len(dirs):
                    break
                if dirs[i] == '.git' or dirs[i] == '_by_tags':
                    del dirs[i]

            for file in files:
                file_path = normalize_path(os.path.join(root, file))
                self.found_names.add(file_path)
                if verbose:
                    sys.stderr.write("adding %s\n" % file_path)

                lfile = file.lower()

                if lfile.endswith('.par2'):
                    self.add_par2(file_path)
                elif lfile.endswith('.sfv'):
                    self.add_sfv(file_path)
                elif lfile.endswith('.md5') or lfile.endswith('.md5sum'):
                    self.add_md5sum(file_path)
                elif lfile.endswith('.shasum') or lfile.endswith('.sha1sum') or \
                        lfile.endswith('.sha256sum') or lfile.endswith('.sha512sum'):
                    self.add_shasum(file_path)
                elif lfile.endswith('.flac'):
                    self.other_data[file_path]['flac'] = True
                elif lfile.endswith('.zip') or lfile.endswith('.cbz'):
                    self.other_data[file_path]['zip'] = True
                elif lfile.endswith('.rar') or lfile.endswith('.cbr'):
                    self.other_data[file_path]['rar'] = True
                elif lfile.endswith('.7z'):
                    self.other_data[file_path]['7z'] = True
                elif lfile.endswith('.jpg') or lfile.endswith('.jpeg'):
                    self.other_data[file_path]['jpeg'] = True
                elif lfile.endswith('.png'):
                    self.other_data[file_path]['png'] = True
                else:
                    for regex in crc32_regexes:
                        res = regex.match(lfile)
                        if res:
                            self.hashes[file_path]['crc32'] = binascii.a2b_hex(res.group(1))
                            break

    def report_for_file(self, path):
        if path not in self.found_names:
            return {'path': path, 'checks': {'not_found': False}, 'skipped': False}
        
        report = dict(path=path, checks={})

        if path in self.skip_verify:
            report['skipped'] = True
            return report
        else:
            report['skipped'] = False

        hashes = self.hashes[path]
        other_data = self.other_data[path]

        if 'length' in other_data:
            actual_size = os.path.getsize(path)
            report['checks']['length'] = actual_size == other_data['length']

        if len(hashes):
            actual_hashes = get_hashes(path, hashes.keys())
            for k, v in hashes.iteritems():
                report['checks'][k] = v == actual_hashes[k]

        return report

    def report_for_all_files(self, parallelism=4):
        pool = multiprocessing.pool.ThreadPool(processes=parallelism)
        return pool.imap(lambda file: self.report_for_file(file), sorted(self.found_names))

    def console_verify(self):
        all_ok = True
        for report in self.report_for_all_files():
            ok = all(report['checks'].values()) or report['skipped']
            if not ok:
                all_ok = False

            if report['skipped'] or len(report['checks']) == 0:
                report_color = 34 # blue
            elif all(report['checks'].values()):
                report_color = 32 # green
            else:
                report_color = 31 # red

            sys.stderr.write("\033[%sm%s\033[m: " % (report_color, report['path']))

            if report['skipped']:
                sys.stderr.write("skipped\n")
            else:
                strings = []
                for check in sorted(report['checks'].keys()):
                    if report['checks'][check]:
                        report_color = 32 # green
                    else:
                        report_color = 31 # red
                    strings.append("\033[%sm%s\033[m" % (report_color, check))
                sys.stderr.write(','.join(strings) + "\n")

        return all_ok

if __name__ == '__main__':
    db = VerificationData()

    if len(sys.argv) == 1:
        db.add_tree('.', verbose=True)
    else:
        for arg in sys.argv[1:]:
            db.add_tree(arg, verbose=True)

    sys.stderr.write("Checking files...\n")
    ret = db.console_verify()

    if ret:
        sys.stderr.write("All files okay!\n")
    else:
        sys.stderr.write("Some files failed!\n")

    sys.exit(0 if ret else 1)
