#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NTESTS 200

int main(int argc, char *argv[]) {

    FILE *fp;

    // Bitwarden
    if(strcmp(argv[1],"bw") == 0) {
        if(strcmp(argv[2],"pin") == 0) {
            fp = fopen("./output/bw_time_pin.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("bw generate --length 4 -n > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        } else if(strcmp(argv[2],"2class12") == 0) {
            fp = fopen("./output/bw_time_2class12.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("bw generate --length 12 -lu > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        } else if(strcmp(argv[2],"3class12") == 0) {
            fp = fopen("./output/bw_time_3class12.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("bw generate --length 12 -lun > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        } else if(strcmp(argv[2],"2class16") == 0) {
            fp = fopen("./output/bw_time_2class16.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("bw generate --length 16 -lu > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        }

    // Jasmin
    } else if(strcmp(argv[1],"jasmin") == 0) {
        if(strcmp(argv[2],"pin") == 0) {
            fp = fopen("./output/jasmin_time_pin.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("node ../../cli/build/bw.js generate --jasminPolicy 4,0,0,0,0,4,4,0,0 > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        } else if(strcmp(argv[2],"2class12") == 0) {
            fp = fopen("./output/jasmin_time_2class12.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("node ../../cli/build/bw.js generate --jasminPolicy 12,0,12,0,12,0,0,0,0 > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        } else if(strcmp(argv[2],"3class12") == 0) {
            fp = fopen("./output/jasmin_time_3class12.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("node ../../cli/build/bw.js generate --jasminPolicy 12,0,12,0,12,0,12,0,0 > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        } else if(strcmp(argv[2],"2class16") == 0) {
            fp = fopen("./output/jasmin_time_2class16.txt","w+");
            clock_t start, end;
            for(int i=0; i<NTESTS; i++) {
                start = clock();
                system("node ../../cli/build/bw.js generate --jasminPolicy 16,0,16,0,16,0,0,0,0 > /dev/null");
                end = clock();
                float seconds = (float)(end - start) / CLOCKS_PER_SEC;
                fprintf(fp,"%f\n",seconds);
            }
            fclose(fp);
        }
    // All
    } else if (strcmp(argv[1],"all") == 0) {
        fp = fopen("./output/bw_time_pin.txt","w+");
        clock_t start, end;
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("bw generate --length 4 -n > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/bw_time_2class12.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("bw generate --length 12 -lu > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/bw_time_3class12.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("bw generate --length 12 -lun > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/bw_time_2class16.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("bw generate --length 16 -lu > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/jasmin_time_pin.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("node ../../cli/build/bw.js generate --jasminPolicy 4,0,0,0,0,4,4,0,0 > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/jasmin_time_2class12.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("node ../../cli/build/bw.js generate --jasminPolicy 12,0,12,0,12,0,0,0,0 > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/jasmin_time_3class12.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("node ../../cli/build/bw.js generate --jasminPolicy 12,0,12,0,12,0,12,0,0 > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);

        fp = fopen("./output/jasmin_time_2class16.txt","w+");
        for(int i=0; i<NTESTS; i++) {
            start = clock();
            system("node ../../cli/build/bw.js generate --jasminPolicy 16,0,16,0,16,0,0,0,0 > /dev/null");
            end = clock();
            float seconds = (float)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp,"%f\n",seconds);
        }
        fclose(fp);
    }
}