# Overview

**Without modifying the submitted artifact**, this file contains the information for: 
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

It indicates that the generated Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1_T.cpp.dl`, and the current implementation satisfies the property. 
Because the property holds at states 2 and 11, and they are the entry states of the two functions defined in the program. 



- Analyze the buggy version of the program (Program 26  X in Table II), which does not satisfy its annotated property: 

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

Totol_execution_time: 0.0692870616913 s
========================================
```

It indicates that the generated Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl`, and the current implementation does not satisfy the property. 
Because the property holds at only state 2, and the second function does not satisfy the property. 

Next, this Datalog file `/home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl` is sent for repair. 


- Repair via the generated Datalog program (Program 26 in Table III): 


```
$ cd ../symlog
$ python run.py lv1 /home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl tmp/lv1 AG_prevClientConnection_eq_0_OR_prevClientConnection_eq_this__IMPLY_AF_handleHTTPCmd_notSupportedPred_Final 12
```

By the end of the console printing, you will see the following: 

```
============================================================
Running lv1 with patched program tmp/lv1/lv1_cpp_dl/lv1.cpp_patch_1.dl, producing Datalog Output: 
---------------
AG_prevClientConnection_eq_0_OR_prevClientConnection_eq_this__IMPLY_AF_handleHTTPCmd_notSupportedPred_Final
===============
2
12
===============


============================================================
Running lv1 with patched program tmp/lv1/lv1_cpp_dl/lv1.cpp_patch_2.dl, producing Datalog Output: 
---------------
AG_prevClientConnection_eq_0_OR_prevClientConnection_eq_this__IMPLY_AF_handleHTTPCmd_notSupportedPred_Final
===============
2
12
===============
```


It indicates that there are two patches generated, and the patched Datalog files are: `/home/symlog/tmp/lv1/lv1_cpp_dl/lv1.cpp_patch_1.dl` and `/home/symlog/tmp/lv1/lv1_cpp_dl/lv1.cpp_patch_2.dl`. 

Moreover, both patched Datalog files are able to output that both functions satisfy the property now. 
*Note that the entry state number of the second function is changed to 12 now; that's because the automatically generated control flow graph of the initially correct code and the buggy code are different.  


- How to check and interpret the repairs: 

The added facts can be seen by the end of these two patched files: 
```
vim /home/symlog/tmp/lv1/lv1_cpp_dl/lv1.cpp_patch_1.dl
# the last line shows: handleHTTPCmd_notSupported(18). // updated fact

vim /home/symlog/tmp/lv1/lv1_cpp_dl/lv1.cpp_patch_2.dl
# the last line shows handleHTTPCmd_notSupported(19). // updated fact
```


The `lv1.cpp_patch_1.dl` repairs the program by adding the fact 'handleHTTPCmd_notSupported(18).', which is a correct patch.   
The `lv1.cpp_patch_2.dl` repairs the program by adding the fact 'handleHTTPCmd_notSupported(19).', which is a correct patch.   
Adding the fact 'handleHTTPCmd_notSupported(18)' or 'handleHTTPCmd_notSupported(19)', indicating to add a function call to 'handleHTTPCmd_notSupported()' in the source code's control flow graph state 18 or 19. 
Both indicate inserting the call in the second if-else branch solves the property violation. 






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
Copy the CTL Datalog files from the ‘Test case locations’ to CTLExpert/repair/ctl-symlog/tests/ctl, strip down all comments, change all .output without (IO=stdout) into .input, and remove (IO=stdout). 

```
$ cd CTLExpert/repair/ctl-symlog
$ python tests/test_symbolic_executor.py
```

The output, which is the solved model for program 27, is displayed in the console. The model corresponds to the repair patch: adding `SSL3_RECORD_set_read(90).` and `SSL3_RECORD_set_read(169).`




### Test case location: 

1. Table 1 (1-15): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/evaluation'`
3. Table 2 (16-25): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/termination`; and
   (26-28): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/protocols`
