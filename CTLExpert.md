# Overview

**Without changing the submitted artifact**, this file contains the information for: 
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

- Analyze a program (Program 26 $\checkmark$ in Table II) which satisfy its annotated property, and the property is 
`AG((prevClientConnection = 0) \/ (prevClientConnection = this_)  => AF(Return(0)))`: 
```
$ cd infer_TempDataLog
$ infer/bin/infer run -- clang -c benchmark/protocols/lv1_T.cpp 
```
By the end of the console printing, you will see the following: 
```
<==
 Runing Datalog $ souffle -F. -D. /home/infer_TempDataLog/benchmark/protocols/lv1_T.cpp.dl 
==>
---------------
AG_prevClientConnection_eq_0_OR_prevClientConnection_eq_this__IMPLY_AF_ReturnPred_Final
===============
2
11
===============
Totol_execution_time: 0.074450969696 s
===============================================
```

It indicates that the generated Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1_T.cpp.dl`, and the current implementation satisfy the property. 
Because the property holds at state 2 and 11, and they are the entry states of the two functions defined in the example. 



- Analyze a program (Program 26  X in Table II) which does not satisfy its annotated property: 

```
$ infer/bin/infer run -- clang -c benchmark/protocols/lv1.cpp 
```
By the end of the console printing, you will see the following: 
```
<==
 Runing Datalog $ souffle -F. -D. /home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl 
==>
---------------
AG_prevClientConnection_eq_0_OR_prevClientConnection_eq_this__IMPLY_AF_handleHTTPCmd_notSupportedPred_Final
===============
2
===============
```

It indicates that the generated Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl`, and the current implementation does not satisfy the property. 
Because the property holds at only state 2, and the second function does not satisfy the property. 


- Repair via the generated Datalog program (Program 26 in Table III): 

Next, the file souffle -F. -D. `/home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl` is sent for repair. 


After repair, the expected output is: 
```
$ souffle -F. -D. /home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl 
---------------
AG_prevClientConnection_eq_0_OR_prevClientConnection_eq_this__IMPLY_AF_handleHTTPCmd_notSupportedPred_Final
===============
2
12
===============
```






# Build From Scratch

Download and unzip the submitted artifact "CTLExpert.zip" from Zenodo: `https://zenodo.org/doi/10.5281/zenodo.13147562`. 

### Setup instructions for the analysis: 
```
$ apt install opam menhir cmake z3 sqlite3 
$ opam init 
$ opam switch create 4.14.0
$ cd CTLExpert/analysis/infer_TempDataLog-main 
$ ./compile  # This takes 3 mins from docker and up to 2 hours from scratch
$ infer/bin/infer --help  # Test the generation of the executable
```
To use the executable: `infer/bin/infer run -- clang -c  [input C program] `. 
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

install required python dependencies
$ cd CTLExpert/repair/ctl-symlog
$ pip install -r requirements.txt
$ pip install -e .
```
<mark> how to test ctl-symlog is built ? </mark>


Converted facts location: `CTLExpert/repair/ctl-symlog/tmp/`

How to run the repair:
Copy the CTL datalog files from the ‘Test case locations’ to CTLExpert/repair/ctl-symlog/tests/ctl, strip down all comments, remove (IO=stdout) and change all .output without (IO=stdout) into .input

```
$ cd CTLExpert/repair/ctl-symlog
$ python tests/test_symbolic_executor.py
```



### Test case location: 

1. Table 1 (1-15): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/evaluation'`
3. Table 2 (16-25): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/termination`; and
   (26-28): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/protocols`
