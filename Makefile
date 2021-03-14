all: compile-jasmin compile-c

compile-jasmin: ./jasminc Jasmin/generatePw.jazz
				./jasminc Jasmin/generatePw.jazz -o asm/generatePw.s

compile-c:	C/passwordGenerator.c asm/generatePw.s
			gcc C/passwordGenerator.c asm/generatePw.s -o exec/passwordGenerator.out


