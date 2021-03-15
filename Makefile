all: compile-jasmin compile-c

compile-jasmin: jasminc Jasmin/generatePw.jazz
				./jasminc Jasmin/generatePw.jazz -o asm/generatePw.s

compile-c:	C/passwordGeneratorApp.c asm/generatePw.s
			gcc C/passwordGeneratorApp.c asm/generatePw.s -o passwordGeneratorApp.out


