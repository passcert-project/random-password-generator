all: compile-jasmin compile-c

compile-jasmin: ../jasmin/compiler/jasminc Jasmin/passCertGenerator.jazz
				../jasmin/compiler/jasminc Jasmin/passCertGenerator.jazz -o passCertGenerator.s

compile-c:	C/passwordGeneratorApp.c passCertGenerator.s
			gcc C/passwordGeneratorApp.c passCertGenerator.s -o passwordGeneratorApp.out


