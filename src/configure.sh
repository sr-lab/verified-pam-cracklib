( echo "-R . Pam" ; find . -name "*.v" -print ) > _CoqProject
coq_makefile -f _CoqProject -o Makefile_Coq
make -f Makefile_Coq
