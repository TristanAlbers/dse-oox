import os
files = os.listdir("verification-tasks\\MinePump")

oox_files = list(filter( lambda x: (".oox" in x), files))


print(len(files))

def main(files, sample_amount_percentage: int):
    # import random
    # files = random.sample(files, int((len(files) * sample_amount_percentage) / 100))
    # print(files)
    for file in files:
        print(file)
        k = 1500
        heuristics = ['concolic-execution']
        

        for h in heuristics:
            command = f'cargo run -- verify verification-tasks\\MinePump\\{file} -f Main.main -k {k} --time-budget 120  --heuristic {h} --run-as-benchmark -q --symbolic-array-size 12'

            result = os.system(command)

main(oox_files, 100)

