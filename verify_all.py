# Apache License 2.0

import sys
import os
import glob

import verify

class VerifyAll:

    def verify_file(self, file, log):
        class ErrorCounter:
            def __init__(self):
                self.count = 0
            def error_handler(self, label, msg):
                self.count += 1
                return False
        error_counter = ErrorCounter()

        urlctx = verify.UrlCtx('', file, sys.stdin)
        ctx = verify.VerifyCtx(urlctx, verify.run, error_counter.error_handler)
        if file == '-':
            url = file
        else:
            url = 'file://' + file
        ctx.run(urlctx, url, ctx, log)
        if error_counter.count != 0:
            print('Found errors in {}'.format(file))
            return False
        else:
            return True

    def verify(self):
        successes = 0
        logname = 'verify.log'
        with open(logname, 'w') as log:
            print('Writing log to {}'.format(logname))
            for root, dirs, files in os.walk('.'):
                for file in glob.iglob(os.path.join(root, '*.gh')):
                    log.write('\nVerifying {}\n'.format(file))
                    if self.verify_file(file, log):
                        successes += 1
            log.write('\nverify_all done\n')

        print('{} files successfully verified'.format(successes))

if __name__ == '__main__':
    if len(sys.argv) != 1:
        print("""
Usage: python verify_all.py

This will verify all .gh files in the current directory and subdirectories.
""")
        sys.exit(1)

    VerifyAll().verify()

