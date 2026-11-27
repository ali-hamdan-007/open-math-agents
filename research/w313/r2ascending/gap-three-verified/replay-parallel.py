import concurrent.futures
import json
import os
from pathlib import Path
import subprocess

home = Path('/workspace/scratch/6893ca6bed01')
lean = home / 'open-math-agents/.oma/elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
os.environ['LEAN_PATH'] = ':'.join([
    str(Path.cwd()), str(home / 'parallel/ramsey/focused'),
    (home / 'parallel/pell/lean-path.txt').read_text().strip(),
])
dag = json.loads(Path('dag.json').read_text())

def check(module):
    with Path(f'{module}.log').open('w') as log:
        subprocess.run([lean, '-j1', '-o', f'{module}.olean', f'{module}.lean'],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    print(f'checked {module}', flush=True)

checked = {'Green145AscendingCore'} | {m for m in dag if Path(f'{m}.olean').is_file()}
pending = dag.keys() - checked
running = {}
workers = int(os.environ.get("LEAN_REPLAY_JOBS", "2"))
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    while pending or running:
        ready = (m for m in dag if m in pending and set(dag[m]) <= checked)
        for module in ready:
            if len(running) == workers:
                break
            pending.remove(module)
            running[pool.submit(check, module)] = module
        if not running:
            raise RuntimeError(f'Blocked DAG modules: {pending}')
        done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
        for job in done:
            module = running.pop(job)
            job.result()
            checked.add(module)
