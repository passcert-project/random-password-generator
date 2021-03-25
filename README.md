# Random Password Generator
The Password Generator component of PassCert. The generator is implemented in Jasmin [1] and will be formally verified with EasyCrypt [2]. This repository has the code of the password generator written in Jasmin and also a small example of a C application using the generator.

## Dependencies
* [Jasmin Compiler](#https://github.com/jasmin-lang/jasmin)
* C compiler (I use *gcc* to compile the example)


## Compiling
### Using the Makefile
Having the compiler executable in the same folder as this repository, makes it possible to simply use

```bash
make
```
 to compile the generator and the C example.

### Without the Makefile
One can also compile separately the Jasmin code and the C code using, respectively,
```bash
./jasminc Jasmin/passCertGenerator.jazz -o asm/passCertGenerator.s
```
```bash
gcc C/passwordGeneratorApp.c asm/passCertGenerator.s -o passwordGeneratorApp.out
```
## Running
```
./passwordGeneratorApp.out
```
## Extracting EasyCrypt from Jasmin program
### Using the Makefile
Having the compiler executable in the same folder as EC, makes it possible to simply use

```bash
make
```
 to extract the EasyCrypt model of the Jasmin program automatically.
 
### Without the Makefile
One can also extract EasyCrypt with the following command
```bash
./jasminc Jasmin/passCertGenerator.jazz -ec generatePassword -oec passCertGenerator_jazz.ec
```


## References
[1]
Almeida, J.B., Barbosa, M., Barthe, G., Blot, A., Grégoire, B., Laporte, V.,
Oliveira, T., Pacheco, H., Schmidt, B., Strub, P.Y.: Jasmin: High-assurance and
high-speed cryptography. In: Proceedings of the 2017 ACM SIGSAC Conference
on Computer and Communications Security. pp. 1807–1823 (2017)

[2]
Barthe, G., Dupressoir, F., Grégoire, B., Kunz, C., Schmidt, B., Strub, P.Y.: Easy-
crypt: A tutorial. In: Foundations of security analysis and design vii, pp. 146–166.
Springer (2013)
