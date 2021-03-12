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
    int lowercaseBool = 0;
    int lowercaseMin = 0;
    int lowercaseMax = 0;
    printf("Do you want lowercase letters in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &lowercaseBool);
    if(lowercaseBool) {
        printf("What is the minimum number of occurrences of lowercase letters in your password?:\n-> ");
        scanf("%d", &lowercaseMin);
        printf("What is the maximum number of occurrences of lowercase letters in your password?:\n-> ");
        scanf("%d", &lowercaseMax);
    }

    // Ask for uppercase letters
    int uppercaseBool = 0;
    int uppercaseMin = 0;
    int uppercaseMax = 0;
    printf("Do you want uppercase letters in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &uppercaseBool);
    if(uppercaseBool) {
        printf("What is the minimum number of occurrences of uppercase letters in your password?:\n-> ");
        scanf("%d", &uppercaseMin);
        printf("What is the maximum number of occurrences of uppercase letters in your password?:\n-> ");
        scanf("%d", &uppercaseMax);
    }

    // Ask for numbers
    int numbersBool = 0;
    int numbersMin = 0;
    int numbersMax = 0;
    printf("Do you want numbers in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &numbersBool);
    if(numbersBool) {
        printf("What is the minimum number of occurrences of number characters in your password?:\n-> ");
        scanf("%d", &numbersMin);
        printf("What is the maximum number of occurrences of number characters in your password?:\n-> ");
        scanf("%d", &numbersMax);
    }

    // Ask for special characters
    int specialBool = 0;
    int specialMin = 1;
    int specialMax = 0;
    printf("Do you want special characters in your password? (1-Yes; 0-No):\n-> ");
    scanf("%d", &specialBool);
    if(specialBool) {
        printf("What is the minimum number of occurrences of special characters in your password?:\n-> ");
        scanf("%d", &specialMin);
        printf("What is the maximum number of occurrences of special characters in your password?:\n-> ");
        scanf("%d", &specialMax);
    }

    // Store policies in array
    uint64_t lowercasePolicies[3];
    lowercasePolicies[0] = (uint64_t) lowercaseBool;
    lowercasePolicies[1] = (uint64_t) lowercaseMin;
    lowercasePolicies[2] = (uint64_t) lowercaseMax;
    uint64_t uppercasePolicies[3];
    uppercasePolicies[0] = (uint64_t) uppercaseBool;
    uppercasePolicies[1] = (uint64_t) uppercaseMin;
    uppercasePolicies[2] = (uint64_t) uppercaseMax;
    uint64_t numbersPolicies[3];
    numbersPolicies[0] = (uint64_t) numbersBool;
    numbersPolicies[1] = (uint64_t) numbersMin;
    numbersPolicies[2] = (uint64_t) numbersMax;
    uint64_t specialPolicies[3];
    specialPolicies[0] = (uint64_t) specialBool;
    specialPolicies[1] = (uint64_t) specialMin;
    specialPolicies[2] = (uint64_t) specialMax;

    // Allocate memory for password to be generated
    char* password = (char*) calloc(length+1, sizeof(char));
    if(password == NULL) {
        printf("Error while allocating memory for password");
    }

    // Generate password
	generatePw((uint64_t) length, (uint64_t) lowercasePolicies, (uint64_t) uppercasePolicies, (uint64_t) numbersPolicies, (uint64_t) specialPolicies, (uint64_t) password);
    
    // Output password
    printf("Random Password: %s\n", password);
    
    // Free memory
    free(password);

	return 1;
}