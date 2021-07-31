#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <inttypes.h>

extern uint64_t generate_password(uint64_t length, uint64_t lowercasePolicies, uint64_t uppercasePolicies, uint64_t numbersPolicies, uint64_t specialPolicies, uint64_t poutput);

int main(int argc, char *argv[]) {

    int length;
    int lowercaseBool, lowercaseMin, lowercaseMax;
    int uppercaseBool, uppercaseMin, uppercaseMax;
    int numbersBool, numbersMin, numbersMax;
    int specialBool, specialMin, specialMax;

    // Check if there is no flag
    if(argc == 1) {
        // Welcome message
        printf("Hi! Welcome to PassCert's password generator!\n");

        // Ask for password length
        printf("Please select the length of your password (1-200):\n-> ");
        scanf("%d", &length);

        // Ask for lowercase letters
        lowercaseBool = 0;
        lowercaseMin = 0;
        lowercaseMax = 0;
        printf("Do you want lowercase letters in your password? (1-Yes; 0-No):\n-> ");
        scanf("%d", &lowercaseBool);
        if(lowercaseBool) {
            printf("What is the minimum number of occurrences of lowercase letters in your password?:\n-> ");
            scanf("%d", &lowercaseMin);
            printf("What is the maximum number of occurrences of lowercase letters in your password?:\n-> ");
            scanf("%d", &lowercaseMax);
        }

        // Ask for uppercase letters
        uppercaseBool = 0;
        uppercaseMin = 0;
        uppercaseMax = 0;
        printf("Do you want uppercase letters in your password? (1-Yes; 0-No):\n-> ");
        scanf("%d", &uppercaseBool);
        if(uppercaseBool) {
            printf("What is the minimum number of occurrences of uppercase letters in your password?:\n-> ");
            scanf("%d", &uppercaseMin);
            printf("What is the maximum number of occurrences of uppercase letters in your password?:\n-> ");
            scanf("%d", &uppercaseMax);
        }

        // Ask for numbers
        numbersBool = 0;
        numbersMin = 0;
        numbersMax = 0;
        printf("Do you want numbers in your password? (1-Yes; 0-No):\n-> ");
        scanf("%d", &numbersBool);
        if(numbersBool) {
            printf("What is the minimum number of occurrences of number characters in your password?:\n-> ");
            scanf("%d", &numbersMin);
            printf("What is the maximum number of occurrences of number characters in your password?:\n-> ");
            scanf("%d", &numbersMax);
        }

        // Ask for special characters
        specialBool = 0;
        specialMin = 0;
        specialMax = 0;
        printf("Do you want special characters in your password? (1-Yes; 0-No):\n-> ");
        scanf("%d", &specialBool);
        if(specialBool) {
            printf("What is the minimum number of occurrences of special characters in your password?:\n-> ");
            scanf("%d", &specialMin);
            printf("What is the maximum number of occurrences of special characters in your password? (0 in case you do not care about the maximum number of occurrences of this set):\n-> ");
            scanf("%d", &specialMax);
        }
    } else if(strcmp(argv[1], "--auto") == 0 || strcmp(argv[1], "-a") == 0) {
        if(argc == 11) {
            length = atoi(argv[2]);
            printf(" ");  //NASTY HACK. THERE IS SOME PROBLEMS WHERE THE PASSWORD IS BEING WRITTEN, AND SOMEHOW THIS SOLVES IT
            lowercaseMin = atoi(argv[3]);
            lowercaseMax = atoi(argv[4]);
            uppercaseMin = atoi(argv[5]);
            uppercaseMax = atoi(argv[6]);
            numbersMin = atoi(argv[7]);
            numbersMax = atoi(argv[8]);
            specialMin = atoi(argv[9]);
            specialMax = atoi(argv[10]);

        } else {
            printf("Use './passwordGeneratorApp.out -h' for help.\n");
            return 1;
        }
    } else if(strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0) {
        printf("TODO");
    } else {
        printf("Use './passwordGeneratorApp.out -h' for help.\n");
        return 1;
    }

    // Store policies in array
    uint64_t lowercasePolicies[2];
    lowercasePolicies[0] = (uint64_t) lowercaseMin;
    lowercasePolicies[1] = (uint64_t) lowercaseMax;
    uint64_t uppercasePolicies[2];
    uppercasePolicies[0] = (uint64_t) uppercaseMin;
    uppercasePolicies[1] = (uint64_t) uppercaseMax;
    uint64_t numbersPolicies[2];
    numbersPolicies[0] = (uint64_t) numbersMin;
    numbersPolicies[1] = (uint64_t) numbersMax;
    uint64_t specialPolicies[2];
    specialPolicies[0] = (uint64_t) specialMin;
    specialPolicies[1] = (uint64_t) specialMax;

    // Allocate memory for password to be generated
    char* password = (char*) calloc(length+1, sizeof(char));
    if(password == NULL) {
        printf("Error while allocating memory for password\n");
    }

    // Generate password
	uint64_t code = generate_password((uint64_t) length, (uint64_t) lowercasePolicies, (uint64_t) uppercasePolicies, (uint64_t) numbersPolicies, (uint64_t) specialPolicies, (uint64_t) password);
    
    if ((int) code == -1) {
        printf("Password length is too large (must be smaller than 200)\n");
    } else if ((int) code == -2) {
        printf("Length can not be negative.\n");
    } else if ((int) code == -3) {
        printf("Lowercase letters minimum number of occurrences can not be negative.\n");
    } else if ((int) code == -4) {
        printf("Uppercase letters minimum number of occurrences can not be negative.\n");
    } else if ((int) code == -5) {
        printf("Numbers minimum number of occurrences can not be negative.\n");
    } else if ((int) code == -6) {
        printf("Special characters minimum number of occurrences can not be negative.\n");
    } else if ((int) code == -7) {
        printf("Lowercase letters maximum number of occurrences can not be smaller than minimum.\n");
    } else if ((int) code == -8) {
        printf("Uppercase letters maximum number of occurrences can not be smaller than minimum.\n");
    } else if ((int) code == -9) {
        printf("Numbers maximum number of occurrences can not be smaller than minimum.\n");
    } else if ((int) code == -10) {
        printf("Special characters maximum number of occurrences can not be smaller than minimum.\n");
    } else if ((int) code == -11) {
        printf("Minimum values sum is too big. It is not possible to satisfy the length with such minimum values.\n");
    } else if ((int) code == -12) {
        printf("Maximum values sum is too small. It is not possible to satisfy the length with such maximum values.\n");
    } else {
        // Output password
        printf("Random Password: %s\n", password);
    }
    
    // Free memory
    free(password);

	return 1;
}