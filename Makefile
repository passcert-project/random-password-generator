all: compile-jasmin compile-c

compile-jasmin: ./jasminc generatePw.jazz
				./jasminc generatePw.jazz -o generatePw.s

compile-c:	passwordGenerator.c generatePw.s
			gcc passwordGenerator.c generatePw.s -o passwordGenerator.out


