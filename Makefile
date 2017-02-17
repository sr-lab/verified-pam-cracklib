main:
	# Compile Coq
	coqc PalindromeProofs.v

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
	ghc -F -pgmF ./fiximports.py -fPIC -dynamic -c PalindromeGenerated.hs -O PalindromeInterface.hs 

	# Compile and link C code with compiled Haskell
	ghc -F -pgmF ./fiximports.py -fPIC -shared -dynamic -o pam_cracklib_v.so PalindromeGenerated.o PalindromeInterface.o pam_cracklib_v.c -lHSrts-ghc7.10.3 -lpam -lcrack

clean:
	rm *.hi *.o *~ *.vo *.glob PalindromeGenerated.* pam_cracklib_v *.so *_stub.h

install:
	# Delete existing installation and copy built installation over
	rm -f /lib/x86_64-linux-gnu/security/pam_cracklib_v.so
	yes | cp -f ./pam_cracklib_v.so /lib/x86_64-linux-gnu/security

activate:
	# Switch to use verified module
	sed -i -e's/pam_cracklib\.so/pam_cracklib_v\.so/g' /etc/pam.d/common-password

deactivate:
	# Switch back to default module
	sed -i -e's/pam_cracklib_v\.so/pam_cracklib\.so/g' /etc/pam.d/common-password
