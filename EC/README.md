# EasyCrypt
In this folder there are all the files related to the Correctness and Security proofs of our implementation, using the [EasyCrypt](#https://www.easycrypt.info/trac) [1] framework.

## Files
* pwGenSpec.ec - The specification of a Random Password Generator (RPG)
* pwGen.eca - RPGs Theory. Here you can see the definitions of Correctness and Security for a RPG
* pwGenSpec_proof.ec - The Correctness and Security proofs of the RPG Specification
* passCertGenerator_jazz.ec - Automatically extracted model of our Jasmin implementation of the RPG Specification
* passCertGenerator_proof.ec - The proof of equivalence between the Jasmin implementation and the RPG Speficication

Array76.ec and WArray76.ec are also automatically generated in the extraction from Jasmin process


## References
[1]
Barthe, G., Dupressoir, F., Grégoire, B., Kunz, C., Schmidt, B., Strub, P.Y.: Easy-
crypt: A tutorial. In: Foundations of security analysis and design vii, pp. 146–166.
Springer (2013)
