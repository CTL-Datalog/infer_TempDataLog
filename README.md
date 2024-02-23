<img src="website/static/img/feiyun.jpeg" alt="logo" width="15%" />


TODO:

1) when \phi1 \/ \phi2 . \phi3
enumerate the behaviors to  (\phi1 . \phi3) \/ (\phi2 . \phi3)
example is the overflow example with EG property

2) delete all the sampling logics, and x==y example to achieve a 
predicate on x and y. 

3) check out the model repair and see the difference


- To compile: 
```./compile  ```

- The first example: 
```
infer/bin/infer run -- clang -c benchmark/evaluation/1.8_potential_termination_1.c
```


infer/bin/infer run -- clang -c benchmark/protocols/pure-ftpd.c

------
./build-infer.sh java
./build-infer.sh clang



git show -s --format=%H
git ls-files | xargs cat | wc -l
git ls-files | xargs wc -l

# biabduction 
# repair 

bidirectional bug localization. 
program synthesis using deductions. 



infer/bin/infer run -- clang -c ../../repair-benchmark/swoole-src/src/core/base.c


1. is that ok to extract the code and analyses it separately 
2. most likely trace to have the repair. 
3. related works derived by "Static automated program repair for heap properties"



AST: 
/Users/yahuis/Desktop/git/infer/infer/src/atd/clang_ast_t.ml


infer/bin/infer run -- clang -c ../DataLogTemp/benchmark/buffer_overflow/1_hostname.c


TODO:
1. add line number to be specifiable, using/adding keyword LINENO to the term type 
2. if-else branch: the fact can only added to the then branch, how to support adding facts to the else branch. 
3. automatically generate type declarations, and the library functions such as "transFlow"
4. support reasoning rules in the specification parts, so that can runnable .dl file directly. 
5. find test cases ranging buffer overflow, alias, and other temporal bugs. 

-- Yahui 6th July. 


TODO: 

1. write specifications and add a spec parser for the test cases. 
2. form a file to track all the test cases and their expected results. 
3. for each test cases, construct the core Datalog output. 

-- Yahui 23 Oct