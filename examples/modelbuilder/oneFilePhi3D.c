#include<stdio.h>
#include <math.h>
#include <stdlib.h>

#define SPEED 1
#define DEFAULT_BORDER_LOCATION -1
#define DEFAULT_BORDER_DISTANCE 100000
#define DEFAULT_INTERIOR_DISTANCE 90000
#define max(a, b) ((a > b) ? a : b)
#define min(a, b) ((a < b) ? a : b)

struct phi_type {
    int x, y, z;
    double dx, dy, dz, F;
    int *location;
    double *distance;
};

typedef struct phi_type Phi;
int max_x, max_xy;

int main() {
    
    void create_phi_function(Phi *);
    void destroy_phi_function(Phi *);
    void update_distance(Phi *, int);
    void set_distance_negative_inside(Phi *, int);
    void adjust_boundary(Phi *);
    void run_fsm(Phi *, int);
    void calc_dist_field(Phi *);
    void fast_sweep(Phi *);
    double solveEikonal(Phi *, int);
    
    
    Phi *pf = (Phi *)malloc(sizeof(Phi));
    if (!pf) {
        printf("Error allocation memory for the phi function.\n");
        exit(1);
        }
        
        create_phi_function(pf);
        
        // print dimensions
        printf("Dimensions:\n");
        printf("x: %d\tdx: %f\n", pf->x, pf->dx);
        printf("y: %d\tdy: %f\n", pf->y, pf->dy);
        printf("z: %d\tdz: %f\n", pf->z, pf->dz);
        
        // print size
        printf("Size:\n");
        printf("x: %d\tdx: %f\n", pf->x, pf->dx);
        printf("y: %d\tdy: %f\n", pf->y, pf->dy);
        printf("z: %d\tdz: %f\n", pf->z, pf->dz);
        
        calc_dist_field(pf);
        
        destroy_phi_function(pf);
        
        free(pf);

    
    return 0;
    
}


void create_phi_function(Phi *pf) {
    
    // initialize fields for the phi function
    pf->x = 255;
    pf->dx = 4.0;
    pf->y = 191;
    pf->dy = 4.0;
    pf->z = 127;
    pf->dz = 1.0;
    pf->F = 1.0;
    printf("%lf",pf->F);
    printf("***");
    // allocate memory for location and distance arrays
    int totalNodes = (pf->x + 2) * (pf->y + 2) * (pf->z + 2);
    pf->location = (int *)malloc(sizeof(int) * totalNodes);
    pf->distance = (double *)malloc(sizeof(double) * totalNodes);
    
    }

void destroy_phi_function(Phi *pf) {
    free(pf->location);
    free(pf->distance);
}
    void update_distance(Phi *pf, int totalNodes) {
    
    int *l = &pf->location[0];
    double *d = &pf->distance[0];
    
    int i;
    for (i = 0; i < totalNodes; i++) {
        if (*l != DEFAULT_BORDER_LOCATION && *d != DEFAULT_BORDER_DISTANCE) {
            //*d = (*l == 1 && *d == DEFAULT_BORDER_DISTANCE)
            //         ? -1
            //         : (*d > 0.0 || *d < 0.0) ? *d : DEFAULT_INTERIOR_DISTANCE;
            *d = (*d > 0.0 || *d < 0.0) ? *d : DEFAULT_INTERIOR_DISTANCE;
            
            
            
        }
        l++;
        d++;
    }
}

    void set_distance_negative_inside(Phi *pf, int totalNodes) {
    
    int *l = &pf->location[0];
    double *d = &pf->distance[0];
    
    
    int i;
    for (i = 0; i < totalNodes; i++) {
        if (*l != DEFAULT_BORDER_LOCATION && *d != DEFAULT_BORDER_DISTANCE) {
            if (*l == 1) {
                *d = -1;
            }
        }
        l++;
        d++;
    }
}

    void adjust_boundary(Phi *pf) {
    
    int x, y, z, i, j, k, xy;
    x = pf->x + 2;
    y = pf->y + 2;
    z = pf->z + 2;
    xy = x * y;
    
    for (i = 0; i < z; i++) {
        for (j = 0; j < y; j++) {
            for (k = 0; k < x; k++) {
                int I = i, J = j, K = k;
                I = (i == z - 1) ? I - 1 : (!i) ? I + 1 : I;
                J = (j == y - 1) ? J - 1 : (!j) ? J + 1 : J;
                K = (k == x - 1) ? K - 1 : (!k) ? K + 1 : K;
                if (i != I || j != J || k != K) {
                    pf->distance[i * xy + j * x + k] = pf->distance[I * xy + J * x + K];
                }
            }
        }
    }
}

double solveEikonal(Phi *pf, int index) {
    
    double dist_new = 0;
    double dist_old = pf->distance[index];
    
    double dx = pf->dx, dy = pf->dy, dz = pf->dz;
    double minX = min(pf->distance[index - 1], pf->distance[index + 1]);
    double minY =
    min(pf->distance[abs(index - max_x)], pf->distance[abs(index + max_x)]);
    double minZ =
    min(pf->distance[abs(index - max_xy)], pf->distance[abs(index + max_xy)]);
    if(dx!= 4.000000 ||dy!=4.000000 || dz != 1.000000){
    printf("%lf",dx);
    printf(",");
    printf("%lf",dy);
    printf(",");
    printf("%lf",dz);
    printf("  ");
    }
    
    double m[] = { minX, minY, minZ };
    double d[] = { dx, dy, dz };
    
    
    // sort the mins
    int i, j;
    double tmp_m, tmp_d;
    for (i = 1; i < 3; i++) {
        for (j = 0; j < 3 - i; j++) {
            
            if (m[j] > m[j + 1]) {
                tmp_m = m[j];
                tmp_d = d[j];
                m[j] = m[j + 1];
                d[j] = d[j + 1];
                m[j + 1] = tmp_m;
                d[j + 1] = tmp_d;
            }
        }
        
    }
    
    // simplifying the variables
    double m_0 = m[0], m_1 = m[1], m_2 = m[2];
    double d_0 = d[0], d_1 = d[1], d_2 = d[2];
    double m2_0 = m_0 * m_0, m2_1 = m_1 * m_1, m2_2 = m_2 * m_2;
    double d2_0 = d_0 * d_0, d2_1 = d_1 * d_1, d2_2 = d_2 * d_2;
    
    if(d2_0==0 || d2_1 ==0)
    {
        printf("%lf",d2_0);
        printf(",");
        printf("%lf",d2_1);
    }
    dist_new = m_0 + d_0;
    if (dist_new > m_1) {
        
        double s = sqrt(-m2_0 + 2 * m_0 * m_1 - m2_1 + d2_0 + d2_1);
        dist_new = (m_1 * d2_0 + m_0 * d2_1 + d_0 * d_1 * s) / (d2_0 + d2_1);
        
        if (dist_new > m_2) {
            
            double a =
            sqrt(-m2_0 * d2_1 - m2_0 * d2_2 + 2 * m_0 * m_1 * d2_2 - m2_1 * d2_0 -
                 m2_1 * d2_2 + 2 * m_0 * m_2 * d2_1 - m2_2 * d2_0 - m2_2 * d2_1 +
                 2 * m_1 * m_2 * d2_0 + d2_0 * d2_1 + d2_0 * d2_2 + d2_1 * d2_2);
            
            dist_new = (m_2 * d2_0 * d2_1 + m_1 * d2_0 * d2_2 + m_0 * d2_1 * d2_2 +
                        d_0 * d_1 * d_2 * a) /
            (d2_0 * d2_1 + d2_0 * d2_2 + d2_1 * d2_2);
        }
    }
    
    
    
    
    return min(dist_old, dist_new);
}


void fast_sweep(Phi *pf) {
    
    int s, i, j, k, index;
    // specifies the sweeping directions
    
    int sweeps[8][3] = { { 1, 1, 1 },
        { 0, 1, 0 },
        { 0, 1, 1 },
        { 1, 1, 0 },
        { 0, 0, 0 },
        { 1, 0, 1 },
        { 1, 0, 0 },
        { 0, 0, 1 } };
    
    printf("Please wait sweeping.....\n");
    for (s = 0; s < 8; ++s) {
        // printf("Fast Sweeping start..... [%d/%d]\n", s, 7);
        
        int iStart = (sweeps[s][0]) ? 1 : pf->z;
        int iEnd = (sweeps[s][0]) ? pf->z + 1 : 0;
        
        int jStart = (sweeps[s][1]) ? 1 : pf->y;
        int jEnd = (sweeps[s][1]) ? pf->y + 1 : 0;
        
        int kStart = (sweeps[s][2]) ? 1 : pf->x;
        int kEnd = (sweeps[s][2]) ? pf->x + 1 : 0;
        
        for (i = iStart; i != iEnd; i = (sweeps[s][0]) ? i + 1 : i - 1) {
            for (j = jStart; j != jEnd; j = (sweeps[s][1]) ? j + 1 : j - 1) {
                for (k = kStart; k != kEnd; k = (sweeps[s][2]) ? k + 1 : k - 1) {
                    index = i * max_xy + j * max_x + k;
                    
                    //printf("%d",solveEikonal(pf,index));
                    pf->distance[index] = solveEikonal(pf, index);
                    //printf("%lf",pf->distance[index]);
                     //printf(",");
                     //printf("  ");
                    
                    
                    
                }
            }
            
        }
    }
    
    
    printf("Sweeping completed.......\n");
}


void run_fsm(Phi *pf, int iterations) {
    
    max_x = pf->x + 2;
    max_xy = max_x * (pf->y + 2);
    
    double start, finish; // for timing
    int itr = 0;
    while (itr++ < iterations) {
        
        // GET_TIME(start);
        
        fast_sweep(pf);
        
        // GET_TIME(finish);
        //printf("Serial FSM time: %f s.\n", finish - start);
    }
}


void calc_dist_field(Phi *pf) {
    
    // get the total number of nodes
    // in the grid
    int totalNodes = (pf->x + 2) * (pf->y + 2) * (pf->z + 2);
    
    // update the distance values
    update_distance(pf, totalNodes);
    
    // use the fast sweeping method
    // to get the solution for the Eikonal Equation
    int itr = 1;
    run_fsm(pf, itr);
    
    // set the distance values to negative
    // for inside region
    set_distance_negative_inside(pf, totalNodes);
    
    adjust_boundary(pf);
}






