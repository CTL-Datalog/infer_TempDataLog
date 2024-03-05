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
infer/bin/infer run -- clang -c benchmark/protocols/pure-ftpd.c           
infer/bin/infer run -- clang -c benchmark/termination/1_Adding_Subtracting_Zero_1_NT.c
```



souffle -F. -D. ef.dl

souffle -t explain ef.dl

explain path(1, 3)

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

