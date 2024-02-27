import os
import subprocess
import time
files = os.listdir("..\\verification-tasks\\algorithms")

files = sorted(files)

oox_files = list(filter( lambda x: (".oox" in x), files))


print(f"Amount of oox files:{len(oox_files)}")

def parser_check():
    '''
    [
        './verification-tasks/algorithms/MergeSortIterative-FunSat02.oox',
        './verification-tasks/algorithms/RedBlackTree-MemUnsat01.oox',
    ]
    '''
    error_files = []

    for file in oox_files:
        error = False
        file_command = f'..\\verification-tasks\\algorithms\\{file}'
        proc = subprocess.Popen(['cargo','run', 'check' , file_command ], stdout=subprocess.PIPE, shell=True)
        (out, err) = proc.communicate()
        # print(f'out: {out}')
        # print(f'err: {err}')
        out_decoded = out.decode()
        if "check OK" in out_decoded:
            error = False
        else:
            error = True
                
        if error:
            error_files.append(file)
            continue

    print(f'\n\nError files: {error_files}')

def verify_verification_tasks():
    
    error_files = []
    disagree_files = []
    agree_files = []

    for file in oox_files:
        k = 2000
        time_budget = 60
        heuristics = ['min-dist2-uncovered']
        invalid = False
        valid = False
        outputs = []
        error = False
        for h in heuristics:
            file_command = f'..\\verification-tasks\\algorithms\\{file}'
            proc = subprocess.Popen(['cargo','run', 'verify' , file_command, '--function', 'Main.main' , '--time-budget', f'{time_budget}', '--heuristic' ,f'{h}'], stdout=subprocess.PIPE, shell=True)
            (out, err) = proc.communicate()
            # print(f'out: {out}')
            # print(f'err: {err}')
            time.sleep(2)
            out_decoded = out.decode()
            outputs.append(out_decoded)
            if "INVALID" in out_decoded:
                invalid = True
            elif "VALID" in out_decoded:
                valid = True
            else:
                error = True
                
        if error:
            error_files.append(file)
            continue
            
        if "Unsat" in file:
            if valid:
                print(f'[ERROR] Disagreement between Jip and SEE in file: {file}\n Jip says: INVALID\n SEE says VALID')
                disagree_files.append(file)
                continue
        elif "Sat" in file:
            if invalid:
                print(f'[ERROR] Disagreement between Jip and SEE in file: {file}\n Jip says: VALID\n SEE says INVALID')
                disagree_files.append(file)
                continue
        agree_files.append(file)

    proc = subprocess.Popen(['cls'], stdout=subprocess.PIPE, shell=True)
    (out, err) = proc.communicate()         

    print(f'Agree files: {agree_files}')
    print(f'Disagree files: {disagree_files}')
    print(f'Error files: {error_files}')

verify_verification_tasks()   
print("end")

        
