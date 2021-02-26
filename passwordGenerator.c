#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern void generatePw(uint64_t length, uint64_t lowercaseBool, uint64_t uppercaseBool, uint64_t numbersBool, uint64_t specialBool, uint64_t poutput);

int main() {
    // Welcome message
    printf("Hi! Welcome to PassCert's password generator!\n");

    // Ask for password length
    int length;
    printf("Please select the length of your password (1-200):\n-> ");
    scanf("%d", &length);

    // Ask for lowercase letters
    int lowercaseBool;
    printf("Do you want lowercase letters in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &lowercaseBool);

    // Ask for uppercase letters
    int uppercaseBool;
    printf("Do you want uppercase letters in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &uppercaseBool);

    // Ask for numbers
    int numbersBool;
    printf("Do you want numbers in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &numbersBool);

    // Ask for special characters
    int specialBool;
    printf("Do you want special characters in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &specialBool);

    // Allocate memory for password to be generated
    char* password = (char*) calloc(length+1, sizeof(char));
    if(password == NULL) {
        printf("Error while allocating memory for password");
    }

    // Generate password
	generatePw((uint64_t) length, (uint64_t) lowercaseBool, (uint64_t) uppercaseBool, (uint64_t) numbersBool, (uint64_t) specialBool, (uint64_t) password);
    
    // Output password
    printf("Random Password: ");
    int i;
    for(i = 0; i < length; i++) {
        printf("%c",password[i]);
    }
    printf("\n");
    
    // Free memory
    free(password);

	return 1;
}