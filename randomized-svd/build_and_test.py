import subprocess, os
os.chdir('/home/pc/work/numerical-algorithms/randomized-svd')
r = subprocess.run(['cargo', 'test', '--test', 'integration', '--', '--nocapture', 'known_low_rank'],
    capture_output=True, text=True, timeout=120)
with open('/tmp/test_out.txt', 'w') as f:
    f.write(r.stdout)
    f.write(r.stderr)
    f.write('\nRC=' + str(r.returncode))
print('RC=' + str(r.returncode))
