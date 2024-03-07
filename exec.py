import os

f = []
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Ar\ArArchiveEntry.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Ar\ArArchiveOutputStream.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Cpio\CpioArchiveEntry.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Cpio\CpioArchiveOutputStream.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Jar\JarArchiveEntry.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Jar\JarArchiveOutputStream.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Tar\TarArchiveEntry.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Tar\TarArchiveOutputStream.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Zip\ZipArchiveEntry.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Zip\ZipArchiveOutputStream.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\ArchiveEntry.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\ArchiveOutputStream.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\ArchiveStreamFactory.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\Main.oox")
f.append(" benchmark_programs\experiment2\defects4j\Compress\Compress_3\oox\StringConstants.oox")

files = ""
for file in f:
    files = files + file

k = 2000
fs = ['original_test','test_symbolic']
heurs = ['min-dist2-uncovered','concolic-execution']
for f in fs:
    print(f'\n[FUNCTION: {f}]\n')
    for h in heurs:
        print(f'\n[HEURISTIC: {h}]\n')
        cmd = f'cargo run -- verify {files} --heuristic {h} --k {k} -f Main.{f}'
        os.system(cmd)