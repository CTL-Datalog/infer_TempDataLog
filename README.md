<img src="website/static/img/logo.png" alt="logo" width="15%" />

# Infer ![build](https://github.com/facebook/infer/actions/workflows/install.yml/badge.svg) ![website](https://github.com/facebook/infer/actions/workflows/deploy.yml/badge.svg)

[Infer](http://fbinfer.com/) is a static analysis tool for Java,
C++, Objective-C, and C. Infer is written in [OCaml](https://ocaml.org/).

## Installation

Read our [Getting
Started](http://fbinfer.com/docs/getting-started) page for
details on how to install packaged versions of Infer. To build Infer
from source, see [INSTALL.md](./INSTALL.md).

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md).

## License

Infer is MIT-licensed.

Note: Enabling Java support may require you to download and install 
components licensed under the GPL.



./build-infer.sh java
./build-infer.sh clang
infer run -- javac examples/Hello.java
infer/bin/infer run -- clang -c examples/Hello.c  
infer/bin/infer run -- clang -c /Users/yahuis/Desktop/git/LightFTP/Source/ftpserv.c
infer/bin/infer run -- clang -c /Users/yahuis/Desktop/git/pure-ftpd/src/main.c



infer/bin/infer run --pulse-only -- clang -c ../../repair-benchmark/my_benchmark/small_test1.c


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


todo:

dataset finding and implementation 

infer/bin/infer run -- clang -c ../../git/swoole-src/src/core/base.cc


instantiate the repair 



/*@  open(path): 
    Post (ret<0, 𝝐) \/ (ret>=0, open(ret))
    Future (ret>=0, (!close(ret))^* · close(ret) · (_)^* )  @*/


/*@  close(handler): 
    Post (TRUE, close(handler)) 
    Future  (TRUE, (!_(handler))^*)  @*/


//NPD
/*@  localtime(t): 
    Future  (ret=0, (!_(ret))^*)  @*/


/*@  malloc(path): 
    Future  (ret=0, (!_(ret))^*)  @*/


/*@  swReactor_get(t, p): 
    Post (ret=0, 𝝐) \/ (!(ret=0), deref(reactor)) 
    Future  (ret=0, (!_(ret))^*)  @*/


// Memory Leak
/*@ malloc(path): 
    Post (ret=0, 𝝐) \/ (!(ret=0), malloc(ret))
    Future (!(ret=0), (!free(ret))^* · free(ret) · (_)^* ) \/ (ret=0, (!_(ret))^*) @*/


/*@ free(handler): 
    Post (TRUE, free(handler)) 
    Future  (TRUE, (!_(handler))^*)  @*/

using the command: 
infer/bin/infer run --pulse-only -- clang -c ../../repair-benchmark/swoole-src/src/core/*


Done with the swoole benchmark, need to do the temporal bugs. 