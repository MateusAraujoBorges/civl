/* http://web.mit.edu/10.001/Web/Course_Notes/NRC_Notes/Gauss_Jordan_NRC.HTML */
/* Program Driver file for gaussj.c routine */
/* Driver for routine for gaussj.c  */
/* Program gauss_driver.c           */ 
#include <stdio.h>
#include <stdlib.h>
#include "nr.h"
#include "nrutil.h" /* Utilities program, listed in Appendix B of NRC book */ 
                    /* NRC stands for Numerical Recipes in C */ 
 
#define MAXSTR 80  
 
int main(void)
{
        int j,k,l,m,n,NP,MP;
        float **a,**ai,**u,**b,**x,**t;
        char dummy[MAXSTR];
        FILE *fp;
/*
* a   is the coefficient matrix.
* ai=a before gaussj is called, ai = inverse(a) after the function call.
* u = ai*a, we define this to test the program, 
*     if correct u should be the unit matrix.
* b = matrix of dimension n*m where m is the number of r.h.s. vectors for which 
*     you want to solve A.x = b.
* x = b before gaussj is called, x is the solution vector after gaussj is called. 
* t is an n*m matrix defined to test the solution. 
*/ 
/*
* Read NP to allocate space for the matrices.  
*/ 
        printf("Input the dimension of the largest square matrix to be used\n");
        scanf("%d",&NP); 
        printf("Input the maximum number of r.h.s. vectors\n");
        scanf("%d",&MP); 
 
        a=matrix(1,NP,1,NP); /* These commands have the same function as calloc */ 
        ai=matrix(1,NP,1,NP);/* They are provided by the utility programs in NRC */ 
        u=matrix(1,NP,1,NP);
        b=matrix(1,NP,1,MP);
        x=matrix(1,NP,1,MP);
        t=matrix(1,NP,1,MP);

	if ((fp = fopen("gaussj.dat","r")) == NULL) 
                nrerror("Data file gaussj.dat not found\n");
			/* See a typical data file appended */ 
        while (!feof(fp)) {
                fgets(dummy,MAXSTR,fp);
                fgets(dummy,MAXSTR,fp);
                fscanf(fp,"%d %d ",&n,&m);
                fgets(dummy,MAXSTR,fp);
                for (k=1;k<=n;k++)
                        for (l=1;l<=n;l++) fscanf(fp,"%f ",&a[k][l]);
                fgets(dummy,MAXSTR,fp);
                for (l=1;l<=m;l++)
                        for (k=1;k<=n;k++) fscanf(fp,"%f ",&b[k][l]);
                /* save matrices for later testing of results */
		for (l=1;l<=n;l++) {
                        for (k=1;k<=n;k++) ai[k][l]=a[k][l];
                        for (k=1;k<=m;k++) x[l][k]=b[l][k];
                }
 
                /* Call gaussj: note that after the call, a is replaced by its 
                   inverse and b is replaced by the solution vector */ 
/*--------------------------------------------------------------------- */  
                gaussj(ai,n,x,m); 
/*--------------------------------------------------------------------- */ 
                printf("\nInverse of matrix a : \n");
                for (k=1;k<=n;k++) {
                        for (l=1;l<=n;l++) printf("%12.6f",ai[k][l]);
                        printf("\n");
                }
                /* check inverse */
                printf("\na times a-inverse:\n");
                for (k=1;k<=n;k++) {
                        for (l=1;l<=n;l++) {
                                u[k][l]=0.0;
                                for (j=1;j<=n;j++)
                                        u[k][l] += (a[k][j]*ai[j][l]);
                        }
                        for (l=1;l<=n;l++) printf("%12.6f",u[k][l]);
                        printf("\n");
                }
                /* check vector solutions */
                printf("\nCheck the following for equality:\n");
                printf("%21s %14s\n","original","matrix*sol'n");
                for (l=1;l<=m;l++) {
                        printf("vector %2d: \n",l);
                        for (k=1;k<=n;k++) {
                                t[k][l]=0.0;
                                for (j=1;j<=n;j++)
                                        t[k][l] += (a[k][j]*x[j][l]);
                                printf("%8s %12.6f %12.6f\n"," ",
                                        b[k][l],t[k][l]);
                        }
                }
        }
        fclose(fp);
        free_matrix(t,1,NP,1,MP);
        free_matrix(x,1,NP,1,MP);
        free_matrix(b,1,NP,1,MP);
        free_matrix(u,1,NP,1,NP);
        free_matrix(ai,1,NP,1,NP);
        free_matrix(a,1,NP,1,NP);
        return 0;
}



