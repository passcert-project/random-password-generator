all: compile-jasmin compile-c

compile-jasmin: ../jasmin/compiler/jasminc Jasmin/passCertRPG.jazz
				../jasmin/compiler/jasminc Jasmin/passCertRPG.jazz -o passCertRPG.s

compile-c:	C/RPG_app.c passCertRPG.s
			gcc C/RPG_app.c passCertRPG.s -o passCertRPG.out


