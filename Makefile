all: compile-jasmin compile-c

compile-jasmin: ../jasmin/compiler/jasminc Jasmin/passCertGenerator.jazz
				../jasmin/compiler/jasminc Jasmin/passCertGenerator.jazz -o asm/passCertGenerator.s

compile-c:	C/passwordGeneratorApp.c asm/passCertGenerator.s
			gcc C/passwordGeneratorApp.c asm/passCertGenerator.s -o passwordGeneratorApp.out


