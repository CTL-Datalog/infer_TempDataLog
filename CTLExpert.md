
Running CTLExpert with examples in Docker. 

```
$ docker pull anonymous716/ctlexpert-main:latest
$ docker run -i -t  anonymous716/ctlexpert-main:latest
$ cd home/infer_TempDataLog/
$ ./compile  # This takes 3 mins from docker and up to 2 hours from scratch 

Analyze the example which satisfy the property: 
$ infer/bin/infer run -- clang -c benchmark/protocols/lv1_T.cpp # This file contains the program which satisfy the property 
```

The following output indicates that the output Datalog file is in `/home/infer_TempDataLog/benchmark/protocols/lv1_T.cpp.dl` 
and the current implementation satisfy the property 
AG((prevClientConnection = 0) \/ (prevClientConnection = this_)  => AF(Return(0)))
Because both state 2 and 11 satisfy it, and they are the entry states of the two functions inside. 

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

Analyze the example which does not satisfy the property: 

$ infer/bin/infer run -- clang -c benchmark/protocols/lv1.cpp # This file contains the program which does not satisfy the property 

The following output indicates that the output Datalog file is in souffle -F. -D. /home/infer_TempDataLog/benchmark/protocols/lv1.cpp.dl 
and the current implementation does not satisfy the property 
AG((prevClientConnection = 0) \/ (prevClientConnection = this_)  => AF(Return(0)))
Because only state 2 satisfies it, and the second function does not satisfy the property. 

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



How to run the analysis:
$ cd CTLExpert/analysis/infer_TempDataLog-main
$ infer/bin/infer run -- clang -c benchmark/evaluation/p1_1.8_potential_termination_1.c 
# The analysis result is printed in the console and the output Datalog file is: benchmark/evaluation/p1_1.8_potential_termination_1.c.dl 

Converted facts location:
CTLExpert/repair/ctl-symlog/tmp/

How to run the repair:
Copy the CTL datalog files from the ‘Test case locations’ to CTLExpert/repair/ctl-symlog/tests/ctl, strip down all comments, remove (IO=stdout) and change all .output without (IO=stdout) into .input

$ cd CTLExpert/repair/ctl-symlog
$ python tests/test_symbolic_executor.py






# Build From Scratch

- SETUP INSTRUCTIONS FOR THE ANALYSIS: 
```
$ apt install opam menhir cmake z3 sqlite3 
$ opam init 
$ opam switch create 4.14.0
$ cd CTLExpert/analysis/infer_TempDataLog-main 
$ ./compile  # This takes 3 mins from docker and up to 2 hours from scratch
$ infer/bin/infer --help  # Test the generation of the executable
```

- SETUP INSTRUCTIONS FOR THE REPAIR: 
1. install conda: https://docs.anaconda.com/miniconda/miniconda-install/ 
2. install clingo through conda: $ conda install -c potassco clingo
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

- TEST CASE LOCATIONS: 

1. Table 1 (1-15): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/evaluation'`
3. Table 2 (16-25): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/termination`; and
   (26-28): `CTLExpert/analysis/infer_TempDataLog-main/benchmark/protocols`
