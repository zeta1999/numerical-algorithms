import subprocess
import os

os.chdir('/home/pc/work/numerical-algorithms/randomized-svd')
result = subprocess.run(
    ['cargo', 'test', '--', '--nocapture'],
    capture_output=True,
    text=True,
    timeout=180
)

with open('/tmp/test_output.txt', 'w') as f:
    f.write('STDOUT:\n')
    f.write(result.stdout[-8000:] if result.stdout else 'NO STDOUT\n')
    f.write('\n\nSTDERR:\n')
    f.write(result.stderr[-3000:] if result.stderr else 'NO STDERR\n')
    f.write('\n\nEXIT CODE: ' + str(result.returncode) + '\n')

print('Output written to /tmp/test_output.txt')
