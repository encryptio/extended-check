#!/usr/bin/env python2

import argparse
import binascii
import cgi
import collections
import hashlib
import multiprocessing
import multiprocessing.pool
import os
import re
import struct
import subprocess
import sys
import zipfile
import zlib

def normalize_path(path):
    """
    Normalize a path to a canonical form, so that different ways to get the
    same path always hit the same dict entries.
    """

    while path.startswith('./'):
        path = path[2:]

    path = re.sub(r'/(\./)+', '/', path)
    path = re.sub(r'(^|/)[^/]+/\.\.(/|$)', r'\1\2', path)
    path = re.sub(r'/+', '/', path)
    
    while path.endswith('/'):
        path = path[:-1]

    return path

class CRC32Hasher(object):
    """
    hashlib-like wrapper for zlib.crc32
    """

    def __init__(self):
        self.crc = zlib.crc32('')

    def update(self, chunk):
        self.crc = zlib.crc32(chunk, self.crc)

    def digest(self):
        return struct.pack('>I', self.crc & 0xffffffff)

def get_hashes(filename, kinds):
    """
    Hashes a file with multiple hash functions, whose names are passed as
    the kinds argument.

    >>> get_hashes("test.txt", ["md5", "sha1", "crc32"])
    {"md5": "...", "sha1": "...", "crc32": "..."}
    """

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

    with open(filename, 'rb', 0) as fh:
        hashers = make_hashers(kinds)
        run_sums(fh, hashers)
        return dict(zip(kinds, map(lambda h: h.digest(), hashers)))

_can_check_zip_external_flag = None
def can_check_zip_external():
    global _can_check_zip_external_flag
    if _can_check_rar_flag is not None:
        return _can_check_rar_flag

    _can_check_zip_external_flag = not subprocess.call('which unzip >/dev/null 2>/dev/null', shell=True)
    return _can_check_zip_external_flag

def check_zip(filename):
    if can_check_zip_external():
        with open(os.devnull, 'w') as null:
            return not subprocess.call(['unzip', '-tqq', filename], stdout=null, stderr=null)
    else:
        # fallback to internal; serializes on the GIL
        try:
            with zipfile.ZipFile(filename, 'r') as zf:
                assert zf.testzip() is None
        except Exception:
            return False
        else:
            return True

_can_check_rar_flag = None
def can_check_rar():
    global _can_check_rar_flag
    if _can_check_rar_flag is not None:
        return _can_check_rar_flag

    _can_check_rar_flag = not subprocess.call('which unrar >/dev/null 2>/dev/null', shell=True)
    return _can_check_rar_flag

def check_rar(filename):
    return not subprocess.call(['unrar', 't', '-inul', '--', filename])

_can_check_flac_flag = None
def can_check_flac():
    global _can_check_flac_flag
    if _can_check_flac_flag is not None:
        return _can_check_flac_flag

    _can_check_flac_flag = not subprocess.call('which flac >/dev/null 2>/dev/null', shell=True)
    return _can_check_flac_flag

def check_flac(filename):
    return not subprocess.call(['flac', '-t', '--totally-silent', filename])

_can_check_png_flag = None
def can_check_png():
    global _can_check_png_flag
    if _can_check_png_flag is not None:
        return _can_check_png_flag

    _can_check_png_flag = not subprocess.call('which pngcheck >/dev/null 2>/dev/null', shell=True)
    return _can_check_png_flag

def check_png(filename):
    with open(os.devnull, 'w') as null:
        return not subprocess.call(['pngcheck', '-q', filename], stdout=null, stderr=null)

class VerificationData(object):
    """
    Provides functions for gathering and verifying a set of files'
    information.
    """

    crc32_regexes = [
        re.compile('.+\[([a-fA-F0-9]{8})\]'),
        re.compile('.+\{([a-fA-F0-9]{8})\}'),
        re.compile('.+\(([a-fA-F0-9]{8})\)'),
        re.compile('.+[^a-zA-Z0-9]([a-fA-F0-9]{8})\.[^.]{3,4}$'),
    ]

    def __init__(self):
        self.found_names = set()
        self.skip_verify = set()
        self.hashes = collections.defaultdict(dict)
        self.other_data = collections.defaultdict(dict)

    def _add_par2(self, file_path):
        self.found_names.add(file_path)
        self.skip_verify.add(file_path)

        base = os.path.dirname(file_path)

        def add_par2_packet(packet):
            # packet contains:
            # 0-15 file id
            # 16-31 md5 hash of entire file
            # 32-47 md5 hash of first 16KiB
            # 48-55 byte length of file
            # 56-end filename, null padded

            file_md5 = packet[16:32]
            file_length = struct.unpack('<Q', packet[48:56])[0]
            file_name = packet[56:]
            while file_name.endswith('\x00'):
                file_name = file_name[:-1]

            path = normalize_path(os.path.join(base, file_name))

            self.hashes[path]['md5'] = file_md5
            self.other_data[path]['length'] = file_length

        def scan_packets(fh):
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

                yield packet_data

        with open(file_path, 'r') as fh:
            for packet in scan_packets(fh):
                add_par2_packet(packet)

    def _add_sfv(self, file_path):
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

    def _add_md5sum(self, file_path):
        self.found_names.add(file_path)
        self.skip_verify.add(file_path)

        base = os.path.dirname(file_path)

        with open(file_path, 'r') as fh:
            for line in fh:
                res = re.match(r'^([a-fA-F0-9]{32})\s[*\s](.+?)\s*$', line)
                if res:
                    path = normalize_path(os.path.join(base, res.group(2)))
                    self.hashes[path]['md5'] = binascii.a2b_hex(res.group(1))

    def _add_shasum(self, file_path):
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

    def add_file(self, path, verbose=False):
        """
        Adds a single file to the database.
        """

        path = normalize_path(path)

        if not os.path.exists(path):
            return

        self.found_names.add(path)
        if verbose:
            sys.stderr.write("adding %s\n" % path)

        lpath = path.lower()

        if lpath.endswith('.par2'):
            self._add_par2(path)
        elif lpath.endswith('.sfv'):
            self._add_sfv(path)
        elif lpath.endswith('.md5') or lpath.endswith('.md5sum'):
            self._add_md5sum(path)
        elif lpath.endswith('.shasum') or lpath.endswith('.sha1sum') or \
                lpath.endswith('.sha256sum') or lpath.endswith('.sha512sum'):
            self._add_shasum(path)
        elif lpath.endswith('.flac'):
            self.other_data[path]['flac'] = True
        elif lpath.endswith('.zip') or lpath.endswith('.cbz'):
            self.other_data[path]['zip'] = True
        elif lpath.endswith('.rar') or lpath.endswith('.cbr'):
            self.other_data[path]['rar'] = True
        elif lpath.endswith('.7z'):
            self.other_data[path]['7z'] = True
        elif lpath.endswith('.jpg') or lpath.endswith('.jpeg'):
            self.other_data[path]['jpeg'] = True
        elif lpath.endswith('.png'):
            self.other_data[path]['png'] = True

        for regex in self.crc32_regexes:
            res = regex.match(lpath)
            if res:
                self.hashes[path]['crc32'] = binascii.a2b_hex(res.group(1))
                break

    def add_tree(self, path, verbose=False):
        """
        Recursively find all verification data in the given path and add it
        to the database.
        """

        ignore_names = set(['.git', '_by_tags', '.DS_Store'])

        if os.path.isfile(path):
            self.add_file(path)
        else:
            for root, dirs, files in os.walk(path):
                for i in range(len(dirs)):
                    if i >= len(dirs):
                        break
                    if dirs[i] in ignore_names:
                        del dirs[i]

                for file in files:
                    if file in ignore_names:
                        continue
                    self.add_file(os.path.join(root, file))

    def report_for_file(self, path):
        """
        Checks a given file with verification data in the database and
        returns a report of the validity of the file.
        """

        if path not in self.found_names:
            return {'path': path, 'checks': {'not_seen': False}, 'skipped': False}

        if not os.path.exists(path):
            return {'path': path, 'checks': {'nonexistent': False}, 'skipped': False}
        
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
        elif 'length_mod_2e32' in other_data:
            actual_size = os.path.getsize(path)
            report['checks']['length_mod_2e32'] = (actual_size & 0xffffffff) == other_data['length_mod_2e32']

        if 'zip' in other_data:
            report['checks']['zip'] = check_zip(path)

        if 'rar' in other_data and can_check_rar():
            report['checks']['rar'] = check_rar(path)

        if 'flac' in other_data and can_check_flac():
            report['checks']['flac'] = check_flac(path)

        if 'png' in other_data and can_check_png():
            report['checks']['png'] = check_png(path)

        if len(hashes):
            actual_hashes = get_hashes(path, hashes.keys())
            for k, v in hashes.iteritems():
                report['checks'][k] = v == actual_hashes[k]

        return report

    def all_reports(self, parallelism=None):
        """
        Returns an iterable of reports for all files in the database.
        """

        if parallelism is None:
            parallelism = multiprocessing.cpu_count() + 1
        pool = multiprocessing.pool.ThreadPool(processes=parallelism)

        all_names = sorted(set(list(self.found_names) + self.hashes.keys() + self.other_data.keys()))
        return pool.imap(lambda file: self.report_for_file(file), all_names)

    def count_reports(self):
        """
        Returns the number of reports that would be returned by all_reports.
        """

        return len(set(list(self.found_names) + self.hashes.keys() + self.other_data.keys()))

class Reporter(object):
    """
    Abstract base class for reporters. Reporters are given a stream of
    reports from a VerificationData instance and should display and/or
    log the data in a reporter-specific manner.
    """

    def start(self):
        """
        Called before iteration begins. Optional.
        """
        pass

    def report(self, report):
        """
        Called for each report yielded from the VerificationData reports.
        """
        raise NotImplementedError()

    def finish(self):
        """
        Called after iteration finishes. Optional.
        """
        pass

class ConsoleReporter(Reporter):
    """
    Reports verification status to the terminal on the given filehandle.
    """

    def __init__(self, fh):
        self.fh = fh

    def start(self):
        self.fh.write("Checking files...\n")
        self.all_ok = True

    def report(self, report):
        if not (report['skipped'] or all(report['checks'].values())):
            self.all_ok = False

        if report['skipped'] or len(report['checks']) == 0:
            report_color = 34 # blue
        elif all(report['checks'].values()):
            report_color = 32 # green
        else:
            report_color = 31 # red

        self.fh.write("\033[%sm%s\033[m: " % (report_color, report['path']))

        if report['skipped']:
            self.fh.write("skipped\n")
        else:
            strings = []
            for check in sorted(report['checks'].keys()):
                if report['checks'][check]:
                    report_color = 32 # green
                else:
                    report_color = 31 # red
                strings.append("\033[%sm%s\033[m" % (report_color, check))
            self.fh.write(','.join(strings) + "\n")

    def finish(self):
        if self.all_ok:
            self.fh.write("No problems found!\n")
        else:
            self.fh.write("Some files failed!\n")

class HTMLReporter(Reporter):
    """
    Reports verification status to an HTML file.
    """

    def __init__(self, html_file):
        self.html_file = html_file

    def start(self):
        self.fh = open(self.html_file, 'wb')
        self.write_header()

    def finish(self):
        self.write_footer()
        self.fh.close()
        del self.fh

    def write_header(self):
        self.fh.write("<html>\n")
        self.fh.write("<head>\n")
        self.fh.write("<style>\n")
        self.fh.write("  .success { background-color: #8f8; border: 1px solid #5c5; padding: 1px 2px; margin-right: 2px; }\n")
        self.fh.write("  .failure { background-color: #f00; border: 1px solid #c00; padding: 1px 2px; margin-right: 2px; color: #fff; }\n")
        self.fh.write("  .unverifiable { background-color: #ccc; border: 1px solid #999; }\n")
        self.fh.write("  .skipped { background-color: #cec; border: 1px solid #9b9; }\n")
        self.fh.write("  td { padding-top: 3px; }\n")
        self.fh.write("  body, td { font-size: small; }\n")
        self.fh.write("</style>\n")
        self.fh.write("</head>\n")
        self.fh.write("<body>\n")
        self.fh.write("<table id=\"verification\">\n")

    def report(self, report):
        if report['skipped']:
            self.fh.write("<tr><td class=\"name skipped\">%s</td></tr>\n" % cgi.escape(report['path']))
            return

        if len(report['checks']) == 0:
            self.fh.write("<tr><td class=\"name unverifiable\">%s</td></tr>\n" % cgi.escape(report['path']))
            return

        self.fh.write("<tr>")
        self.fh.write("<td class=\"name\">%s</td>" % cgi.escape(report['path']))

        self.fh.write("<td class=\"checks\">")
        for check in report['checks'].iterkeys():
            _class = 'success' if report['checks'][check] else 'failure'
            self.fh.write("<span class=\"%s\">%s</span>" % (_class, cgi.escape(check)))
        self.fh.write("</td>")

        self.fh.write("</tr>\n")

    def write_footer(self):
        self.fh.write("</table>\n")
        self.fh.write("</body>\n")
        self.fh.write("</html>\n")

def main(py_exec_name, *args):
    parser = argparse.ArgumentParser(description='Check validity of files')
    parser.add_argument('-v', '--verbose', default=False, action='store_true')
    parser.add_argument('-p', '--progress', default=False, action='store_true')
    parser.add_argument('--html', help='Save a report to this HTML file')
    parser.add_argument('paths', default=['.'], nargs='*')
    options = parser.parse_args(args)

    reporters = []
    if options.verbose:
        reporters.append(ConsoleReporter(fh=sys.stderr))
    if options.html:
        reporters.append(HTMLReporter(options.html))

    db = VerificationData()
    for path in options.paths:
        db.add_tree(path, verbose=options.verbose)

    for reporter in reporters:
        reporter.start()

    if options.progress:
        sys.stderr.write("\r\033[K0/%s" % db.count_reports())

    all_ok = True
    report_index = 1
    for report in db.all_reports():
        if options.progress:
            sys.stderr.write("\r\033[K")

        for reporter in reporters:
            reporter.report(report)

        if options.progress:
            sys.stderr.write("\r\033[K%s/%s" % (report_index, db.count_reports()))

        if not (report['skipped'] or all(report['checks'].values())):
            all_ok = False

        report_index += 1

    if options.progress:
        sys.stderr.write("\r\033[K")

    for reporter in reporters:
        reporter.finish()

    sys.exit(0 if all_ok else 1)

if __name__ == '__main__':
    main(*sys.argv)
