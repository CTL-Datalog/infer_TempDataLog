# Overview

This file contains the information for: 
- Instructions for testing CTLExpert from Docker
- Instructions for building CTLExpert from scratch


# Running CTLExpert with examples in Docker

- Obtain the docker image 
```
$ docker pull anonymous716/ctlexpert-main:latest
$ docker run -i -t  anonymous716/ctlexpert-main:latest
$ cd home
$ ls 
# there are two folders: infer_TempDataLog and symlog
```

- Analyze a program (Program 26 $\checkmark$ in Table II) that satisfy its annotated property, and the property is 
`AG((prevClientConnection = 0) \/ (prevClientConnection = this_)  => AF(handleHTTPCmd_notSupported()))`: 
```
$ cd infer_TempDataLog
$ infer/bin/infer run -- clang -c benchmark/protocols/2_lv5_T.cpp
```
By the end of the console printing, you will see the following: 
```
 Runing Datalog $ souffle -F. -D. /home/infer_TempDataLog/benchmark/protocols/2_lv5_T.cpp.dl 
==>
---------------
AG_tmp_lteq_1_IMPLY_AF_parseSucceeded_eq_0_Final
===============
0
===============

Totol_execution_time: 0.190281867981 s
=========================================================================
```

It indicates that the generated Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1_T.cpp.dl`, and the current implementation satisfies the property. 
Because the property holds at state 0, and it is the entry state of the two functions defined in the program. 



- Analyze the buggy version of the program (Program 26  X in Table II), which does not satisfy its annotated property: 

```
$ infer/bin/infer run -- clang -c benchmark/protocols/2_lv5.cpp
```
By the end of the console printing, you will see the following: 
```
 Runing Datalog $ souffle -F. -D. /home/infer_TempDataLog/benchmark/protocols/2_lv5.cpp.dl 
==>
---------------
AG_tmp_lteq_1_IMPLY_AF_parseSucceeded_eq_0_Final
===============
===============

Totol_execution_time: 0.192929983139 s
=========================================================================
```

It indicates that the generated Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl`, and the current implementation does not satisfy the property. 
Because the property does not hold at the entry state.

Next, this Datalog file `/home/infer_TempDataLog/benchmark/protocols/2_lv5.cpp.dl` is sent for repair. 


- Repair via the generated Datalog program (Program 26 in Table III): 


```
$ cd ../symlog
$ python run.py lv5 /home/infer_TempDataLog/benchmark/protocols/2_lv5.cpp.dl tmp/2_lv5 AG_tmp_lteq_1_IMPLY_AF_parseSucceeded_eq_0_Final 0
```

By the end of the console printing, you will see the following: 

```
Time taken: 0.46761131286621094
============================================================
Running lv5 with patched program tmp/lv5/2_lv5_cpp_dl/2_lv5.cpp_patch_1.dl, producing Datalog Output: 
---------------
NotTotal
===============
===============
---------------
AG_tmp_lteq_1_IMPLY_AF_parseSucceeded_eq_0_Final
===============
0
===============
```

It indicates that one patch was finally selected, and the patched Datalog file is: `/home/symlog/tmp/lv5/2_lv5_cpp_dl/2_lv5.cpp_patch_1.dl`. 


- How to check and interpret the repairs: 

The added facts can be seen by the end of the patched Datalog file: 
```
vim /home/symlog/tmp/lv5/2_lv5_cpp_dl/2_lv5.cpp_patch_1.dl

// ========== Patch Summary ==========
// Added facts:
// + Eq("parseSucceeded", 10, 0).
// Removed facts:
// - NotEq("parseSucceeded", 10, 0).
```


The `2_lv5.cpp_patch_1.dl` repairs the program by changing the fact `NotEq("parseSucceeded", 10, 0).` to `Eq("parseSucceeded", 10, 0).`. 
This indicates that changing the assignment of `parseSucceeded` at state 10 to 0 solves the property violation. 


# Reproduce the Table 1, 2 and 3 
```
./run_table_1
./run_table_2
./run_table_3
```



# Build From Scratch

Download and unzip the submitted artifact "CTLExpert.zip" from Zenodo: `https://zenodo.org/doi/10.5281/zenodo.13147562`. 

### Setup instructions for the analysis: 
```
$ apt install opam menhir cmake z3 sqlite3 
$ opam init 
$ opam switch create 4.14.0
$ git clone https://github.com/CTL-Datalog/infer_TempDataLog.git
$ cd CTLExpert/analysis/infer_TempDataLog-main 
$ ./compile  # This takes 3 mins from docker and up to 2 hours from scratch
$ infer/bin/infer --help  # Test the generation of the executable
```
To use the executable: `infer/bin/infer run -- clang -c  [Input C Program] `. 
For example: 
```
$ infer/bin/infer run -- clang -c benchmark/protocols/pure-ftpd_T.c
``` 
The analysis result is printed in the console and the output Datalog file is: `/home/infer_TempDataLog/benchmark/protocols/pure-ftpd_T.c.dl `


### Setup instructions for the repair: 
1. install conda: https://docs.anaconda.com/miniconda/miniconda-install/ 
2. install clingo through conda: 
```
$ conda install -c potassco clingo
```
3. install Souffle: 
```
$ wget -P /tmp https://github.com/souffle-lang/souffle/releases/download/2.2/x86_64-ubuntu-2104-souffle-2.2-Linux.deb
$ sudo dpkg -i /tmp/x86_64-ubuntu-2104-souffle-2.2-Linux.deb
$ sudo apt-get install -f
$ rm /tmp/x86_64-ubuntu-2104-souffle-2.2-Linux.deb
```

4. install required python dependencies
```
$ cd CTLExpert/repair/ctl-symlog
$ pip install -r requirements.txt
$ pip install -e .
```

How to run the repair:

```
$ cd CTLExpert/repair/ctl-symlog
$ python run.py 1_pure_ftpd /home/infer_TempDataLog/benchmark/protocols/1_pure-ftpd.c.dl tmp/1_pure_ftpd AG_temp_lt_0_IMPLY_AF_overflow_gt_0_Final 0
```

Two patches were generated and can be found at:
- `/home/symlog/tmp/1_pure_ftpd/1_pure-ftpd_c_dl/1_pure-ftpd.c_patch_1.dl`
- `/home/symlog/tmp/1_pure_ftpd/1_pure-ftpd_c_dl/1_pure-ftpd.c_patch_2.dl`

The patches make the following changes:
1. Patch 1 removes the fact `Lt("temp", 7, 0).`, which corresponds to adding `if (temp < 0) { return; }` in the source code
2. Patch 2 removes the fact `Lt("max_filesize", 5, 0).`, which corresponds to adding `if (max_filesize < 0) { return; }` in the source code




### Test case location: 

1. Table 1 (1-15): `CTLExpert/infer_TempDataLog-main/benchmark/evaluation'`
3. Table 2 (16-25): `CTLExpert/infer_TempDataLog-main/benchmark/termination`; and
   (26-28): `CTLExpert/infer_TempDataLog-main/benchmark/protocols`
