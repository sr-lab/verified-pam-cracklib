# Override shell executable from sh to bash
SHELL:=/bin/bash

main:
	# Compile and make Coq project
	( echo "-R . Hapsl" ; find . -name "*.v" -print ) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile_Coq
	make -f Makefile_Coq

	#| Command     | Description                                             |
	#|-------------|---------------------------------------------------------|
	#| -F          | Enable the use of a pre-processor (set with -pgmF)      |
	#| -pgmF <cmd> | Use cmd as the pre-processor (with -F only)             |
	#| -fPIC       | Generate position-independent code (where available)    |
	#| -dynamic    | Use dynamic Haskell libraries (if available)            |
	#| -c          | Do not link                                             |
	#| -O          | Enable default optimisation (level 1)                   |
	#| -shared     | Generate a shared library (as opposed to an executable) |
	#| -l<lib>     | Link in library lib                                     |
	#| -o          | set output filename                                     |

	# Compile Haskell to object code (*.o) but do not link
	ghc -F -pgmF ./fiximports.py -fPIC -dynamic -c PamGenerated.hs -O PamInterface.hs 

	# Compile and link C code with compiled Haskell
	ghc -F -pgmF ./fiximports.py -fPIC -shared -dynamic -o pam_basic_pwd_policy.so PamGenerated.o PamInterface.o pam_basic_pwd_policy.c -lHSrts-ghc7.10.3 -lpam -lcrack 

clean:
	rm -f *.hi *.o .*.aux *~ *.vo *.glob PamGenerated.* pam_basic_pwd_policy *.so *_stub.h

install:
	# Delete existing installation and copy built installation over
	rm -f /lib/x86_64-linux-gnu/security/pam_basic_pwd_policy.so
	yes | cp -f ./pam_basic_pwd_policy.so /lib/x86_64-linux-gnu/security
	rm -f /lib/security/pam_basic_pwd_policy.so
	yes | cp -f ./pam_basic_pwd_policy.so /lib/security

activate:
	# Switch to use verified module
	sed -i -e's/pam_cracklib\.so.*/pam_basic_pwd_policy\.so/g' /etc/pam.d/common-password

deactivate:
	# Switch back to default module
	sed -i -e's/pam_basic_pwd_policy\.so/pam_cracklib\.so retry=3 minlen=8 difok=3 maxclassrepeat=2/g' /etc/pam.d/common-password
