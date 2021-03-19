all: compile-jasmin compile-c

compile-jasmin: jasminc Jasmin/passCertGenerator.jazz
				./jasminc Jasmin/passCertGenerator.jazz -o asm/passCertGenerator.s

compile-c:	C/passwordGeneratorApp.c asm/passCertGenerator.s
			gcc C/passwordGeneratorApp.c asm/passCertGenerator.s -o passwordGeneratorApp.out


