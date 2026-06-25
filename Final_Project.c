#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_AIR_ROUTES 5
#define WHITE 0
#define GRAY  1
#define BLACK 2
#define INF  2147483647
#define CACHE_SIZE 4096

typedef struct {
    int x,y;
} Punto;

typedef struct RottaAerea {
    int x_dest;
    int y_dest;
    int costo_rotta;
    struct RottaAerea *next;
} RottaAerea;

typedef struct {
    int costo_esagono;
    int num_rotte_aeree;
    int somma_costi_rotta;
    RottaAerea *rotte_aeree;
    int color;
    int distanza;
} Esagono;

typedef struct {
    int x,y;
    int dist;
} HeapNode;

// CACHE
typedef struct {int x1 ,y1 ,x2 ,y2;} HashKey;
typedef struct {
    HashKey key;
    int costo;
} CacheEntry;

CacheEntry cache[CACHE_SIZE];
int cache_valid[CACHE_SIZE];


Esagono **mappa = NULL;
int n_colonne,n_righe = 0;


int **distanze;
int **pos_in_heap;
int **visitato;
int **distanze_timestamp;
int current_run_id = 1;

Punto *queue;
int q_head, q_tail, q_size;

HeapNode* heap_global = NULL;
int heap_global_capacity = 0;

Punto *touched;
int touched_size = 0;


const int dx_even[6] = { -1, -1,  0,  0, +1, +1 };
const int dy_even[6] = {  0, -1, -1, +1,  0, -1 };
const int dx_odd[6]  = { -1, -1,  0,  0, +1, +1 };
const int dy_odd[6]  = {  0, +1, -1, +1,  0, +1 };

// METODI HEAP
void init_heap_global() {
    if (heap_global_capacity < n_righe*n_colonne) {
        free(heap_global);
        heap_global = malloc(n_righe*n_colonne*sizeof(HeapNode));
        heap_global_capacity = n_righe*n_colonne;
    }
}
void free_heap_global() {
    free(heap_global);
    heap_global=NULL;
    heap_global_capacity=0;
}
void heap_swap(int a, int b) {
    HeapNode tmp = heap_global[a];
    heap_global[a] = heap_global[b];
    heap_global[b] = tmp;
    pos_in_heap[heap_global[a].x][heap_global[a].y] = a;
    pos_in_heap[heap_global[b].x][heap_global[b].y] = b;
}
void heap_up(int i) {
    while (i > 0) {
        int p = (i - 1) >> 1;
        if (heap_global[i].dist < heap_global[p].dist) {
            heap_swap(i, p);
            i = p;
        } else break;
    }
}
void heap_down(int heap_size,int i) {
    while (1) {
        int l = (i << 1) + 1;
        int r = (i << 1) + 2;
        int smallest = i;
        if (l < heap_size && heap_global[l].dist < heap_global[smallest].dist) smallest = l;
        if (r < heap_size && heap_global[r].dist < heap_global[smallest].dist) smallest = r;
        if (smallest != i) {
            heap_swap(i, smallest);
            i = smallest;
        } else break;
    }
}
void heap_push(int* heap_size,int x, int y, int dist) {
    heap_global[*heap_size] = (HeapNode){x, y, dist};
    pos_in_heap[x][y] = *heap_size;
    (*heap_size)++;
    heap_up(*heap_size - 1);
}
HeapNode heap_pop(int* heap_size) {
    HeapNode min = heap_global[0];
    pos_in_heap[min.x][min.y] = -1;
    (*heap_size)--;
    if (*heap_size > 0) {
        heap_global[0] = heap_global[*heap_size];
        pos_in_heap[heap_global[0].x][heap_global[0].y] = 0;
        heap_down(*heap_size,0);
    }
    return min;
}
void heap_decrease_key(int x, int y, int new_dist) {
    int i = pos_in_heap[x][y];
    if (i == -1) return;
    heap_global[i].dist = new_dist;
    heap_up(i);
}


unsigned int hash_key(HashKey k) {
    unsigned int h = 0;
    h = (unsigned)k.x1 * 31u;
    h ^= (unsigned)k.y1 * 131u;
    h ^= (unsigned)k.x2 * 811u;
    h ^= (unsigned)k.y2 * 2137u;
    return h % CACHE_SIZE;
}
int cache_lookup(HashKey k) {
    unsigned int h = hash_key(k);
    for (int i = 0;i<CACHE_SIZE;i++) {
        unsigned int pos = (h+i) % CACHE_SIZE;
        if (!cache_valid[pos]) return -1;
        if (cache[pos].key.x1==k.x1 && cache[pos].key.y1==k.y1 &&
            cache[pos].key.x2==k.x2 && cache[pos].key.y2==k.y2) {
            return cache[pos].costo;
        }
    }
    return -1;
}
void cache_insert(HashKey k,int costo) {
    unsigned int h = hash_key(k);
    for (int i = 0;i<CACHE_SIZE;i++) {
        unsigned int pos = (h+i) % CACHE_SIZE;
        if (!cache_valid[pos]) {
            cache_valid[pos] = 1;
            cache[pos].key=k;
            cache[pos].costo=costo;
            return;
        }
    }
    cache[h].key=k;
    cache[h].costo=costo;
    cache_valid[h]=1;
}
void cache_delete() {
    for (int i = 0;i<CACHE_SIZE;i++) {
        cache_valid[i] = 0;
    }
}


int getVicini(int x, int y, Punto* vicini) {
    int count = 0;
    const int *dx = (x & 1) ? dx_odd : dx_even;
    const int *dy = (x & 1) ? dy_odd : dy_even;
    for (int i = 0; i < 6; i++) {
        int nx = x + dx[i];
        int ny = y + dy[i];
        if ((unsigned)nx < (unsigned)n_righe &&
            (unsigned)ny < (unsigned)n_colonne) {
            vicini[count++] = (Punto){nx, ny};
        }
    }
    return count;
}
static int floor_div(int a, int b) {
    if (a >= 0) return a / b;
    return - ( ( -a + b - 1 ) / b );
}
int formulaDelta(Esagono e, int v, int raggio) {
    int diff = raggio - e.distanza;
    if (diff<0) return 0;
    int numer = v * diff;
    return floor_div(numer, raggio);
}


void dealloca() {
    if (mappa == NULL) return;
    for (int i = 0; i < n_righe; i++) {
        for (int j = 0; j < n_colonne; j++) {
            RottaAerea *current = mappa[i][j].rotte_aeree;
            while (current != NULL) {
                RottaAerea *next = current->next;
                free(current);
                current = next;
            }
        }
        free(distanze[i]);
        free(pos_in_heap[i]);
        free(visitato[i]);
        free(distanze_timestamp[i]);
        free(mappa[i]);
    }
    free(distanze);
    free(pos_in_heap);
    free(visitato);
    free(distanze_timestamp);
    free(mappa);
    free(queue);
    free(touched);
    distanze=NULL; pos_in_heap=NULL; visitato=NULL; distanze_timestamp=NULL;
    mappa=NULL; queue=NULL; touched=NULL;
    n_colonne=0; n_righe=0;
    free_heap_global();
    cache_delete();
}

// INIT
void init(int x ,int y) {
    if (mappa != NULL) dealloca();
    n_colonne = x;
    n_righe = y;
    mappa= (Esagono**)malloc(n_righe*sizeof(Esagono*));
    distanze = (int**)malloc(n_righe * sizeof(int*));
    pos_in_heap = (int**)malloc(n_righe * sizeof(int*));
    visitato = (int**)malloc(n_righe * sizeof(int*));
    distanze_timestamp = (int**)malloc(n_righe * sizeof(int*));
    q_size=n_righe*n_colonne;
    queue=malloc(q_size * sizeof(Punto));
    touched = malloc(n_righe * n_colonne * sizeof(Punto));

    for (int i = 0; i < n_righe; i++) {
        mappa[i] = (Esagono*)malloc(n_colonne*sizeof(Esagono));
        distanze[i] = (int*)malloc(n_colonne*sizeof(int));
        pos_in_heap[i]= (int*)malloc(n_colonne*sizeof(int));
        visitato[i]= (int*)malloc(n_colonne*sizeof(int));
        distanze_timestamp[i]= (int*)malloc(n_colonne*sizeof(int));
        for (int j = 0; j < n_colonne; j++) {
            mappa[i][j].costo_esagono = 1;
            mappa[i][j].num_rotte_aeree = 0;
            mappa[i][j].somma_costi_rotta = 0;
            mappa[i][j].color= WHITE;
            mappa[i][j].distanza = 0;
            mappa[i][j].rotte_aeree = NULL;
            distanze[i][j] = INF;
            pos_in_heap[i][j] = -1;
            visitato[i][j] = 0;
            distanze_timestamp[i][j]=0;
        }
    }
    for (int i = 0; i < CACHE_SIZE; i++) cache_valid[i]=0;
    init_heap_global();
    printf("OK\n");
}


void toggle_air_route(int y1, int x1, int y2, int x2) {
    if (x1<0||x1>=n_righe||y1<0||y1>=n_colonne||
        x2<0||x2>=n_righe||y2<0||y2>=n_colonne){
        printf("KO\n");
        return;
    }
    Esagono *e1= &mappa[x1][y1];
    cache_delete();
    RottaAerea *current = e1->rotte_aeree, *prev=NULL;
    while (current!=NULL) {
        if (current->x_dest==x2 && current->y_dest==y2) {
            if (prev==NULL) e1->rotte_aeree=current->next;
            else prev->next=current->next;
            e1->num_rotte_aeree--;
            e1->somma_costi_rotta -= current->costo_rotta;
            free(current);
            printf("OK\n");
            return;
        }
        prev=current;
        current=current->next;
    }
    if (e1->num_rotte_aeree >= MAX_AIR_ROUTES) {
        printf("KO\n");
        return;
    }
    int costo_medio;
    if (e1->num_rotte_aeree==0) costo_medio=e1->costo_esagono;
    else costo_medio=(e1->somma_costi_rotta + e1->costo_esagono) / (e1->num_rotte_aeree + 1);
    if (costo_medio<0) costo_medio=0;
    if (costo_medio>100) costo_medio=100;
    RottaAerea *nuova=malloc(sizeof(RottaAerea));
    nuova->x_dest=x2;
    nuova->y_dest=y2;
    nuova->costo_rotta=costo_medio;
    nuova->next=e1->rotte_aeree;
    e1->rotte_aeree=nuova;
    e1->num_rotte_aeree++;
    e1->somma_costi_rotta += costo_medio;
    printf("OK\n");
}


void change_cost(int y1 , int x1 , int v , int raggio ) {
    if (y1<0|| y1>=n_colonne ||x1<0 ||x1>=n_righe) {
        printf("KO\n");
        return;
    }
    if (v<-10|| v>10|| raggio<=0) {
        printf("KO\n");
        return;
    }
    cache_delete();

    q_head = 0;
    q_tail = 0;
    mappa[x1][y1].color = GRAY;
    mappa[x1][y1].distanza = 0;
    queue[q_tail++] = (Punto){x1, y1};

    while (q_head < q_tail) {
        Punto p = queue[q_head++];
        Esagono *e = &mappa[p.x][p.y];

        int delta = formulaDelta(*e, v, raggio);


        int old_es = e->costo_esagono;
        int new_es = old_es + delta;
        if (new_es < 0) new_es = 0;
        if (new_es > 100) new_es = 100;
        e->costo_esagono = new_es;


        for (RottaAerea *r = e->rotte_aeree; r; r = r->next) {
            int old_cost = r->costo_rotta;
            int new_cost = old_cost + delta;
            if (new_cost < 0) new_cost = 0;
            if (new_cost > 100) new_cost = 100;
            r->costo_rotta = new_cost;
            e->somma_costi_rotta += (new_cost - old_cost);
        }

        if (e->distanza + 1 < raggio) {
            Punto vicini[6];
            int n_vicini = getVicini(p.x, p.y, vicini);
            for (int i = 0; i < n_vicini; i++) {
                Esagono *ev = &mappa[vicini[i].x][vicini[i].y];
                if (ev->color == WHITE) {
                    ev->color = GRAY;
                    ev->distanza = e->distanza + 1;
                    queue[q_tail++] = vicini[i];
                }
            }
        }
    }

    //uso solo quelli toccati
    for (int i = 0; i < q_tail; i++) {
        mappa[queue[i].x][queue[i].y].color = WHITE;
        mappa[queue[i].x][queue[i].y].distanza = 0;
    }
    printf("OK\n");
}



int travel_cost(int yp, int xp, int yd , int xd) {
    if (xp<0||xp>=n_righe||yp<0||yp>=n_colonne||xd<0
        ||xd>=n_righe||yd<0||yd>=n_colonne) {
        return -1;
    }

    if (xp==xd && yp==yd) {
        return 0;
    }

    HashKey k={.x1=xp,.y1=yp,.x2=xd,.y2=yd};
    int cached = cache_lookup(k);
    if (cached != -1) {
        return cached;
    }

    int heap_size = 0;
    current_run_id++;

    // inizializza sorgente
    distanze[xp][yp] = 0;
    distanze_timestamp[xp][yp] = current_run_id;
    pos_in_heap[xp][yp] = -1;
    heap_push(&heap_size, xp, yp, 0);

    while (heap_size > 0) {
        HeapNode u = heap_pop(&heap_size);

        if (visitato[u.x][u.y] == current_run_id) continue;
        visitato[u.x][u.y] = current_run_id;

        if (u.x == xd && u.y == yd) {
            cache_insert(k, u.dist);
            return u.dist;
        }

        Esagono *e = &mappa[u.x][u.y];

        if (e->costo_esagono > 0 ) {
            const int *dx = (u.x & 1) ? dx_odd : dx_even;
            const int *dy = (u.x & 1) ? dy_odd : dy_even;

            for (int i = 0; i < 6; i++) {
                int vx = u.x + dx[i];
                int vy = u.y + dy[i];
                if ((unsigned)vx >= (unsigned)n_righe || (unsigned)vy >= (unsigned)n_colonne) continue;
                int nuova = u.dist + e->costo_esagono;


                if (distanze_timestamp[vx][vy] != current_run_id) {
                    distanze[vx][vy] = nuova;
                    distanze_timestamp[vx][vy] = current_run_id;
                    pos_in_heap[vx][vy] = -1;
                } else {
                    if (nuova >= distanze[vx][vy]) continue;
                    distanze[vx][vy] = nuova;
                }

                if (pos_in_heap[vx][vy] == -1)
                    heap_push(&heap_size, vx, vy, distanze[vx][vy]);
                else
                    heap_decrease_key(vx, vy, distanze[vx][vy]);
            }
        }

        for (RottaAerea *r = e->rotte_aeree; r; r = r->next) {
            if (r->costo_rotta <= 0) continue;

            int ax = r->x_dest, ay = r->y_dest;
            if ((unsigned)ax >= (unsigned)n_righe || (unsigned)ay >= (unsigned)n_colonne) continue;
            int nuova = u.dist + r->costo_rotta;

            if (distanze_timestamp[ax][ay] != current_run_id) {
                distanze[ax][ay] = nuova;
                distanze_timestamp[ax][ay] = current_run_id;
                pos_in_heap[ax][ay] = -1;
            } else {
                if (nuova >= distanze[ax][ay]) continue;
                distanze[ax][ay] = nuova;
            }

            if (pos_in_heap[ax][ay] == -1)
                heap_push(&heap_size, ax, ay, distanze[ax][ay]);
            else
                heap_decrease_key(ax, ay, distanze[ax][ay]);
        }
    }
    return -1;
}


int main(void) {
    char comando [30];

    while (scanf("%s", comando) != EOF) {
        if (strcmp(comando, "init") == 0) {
            int col, rig;
            if (scanf("%d %d", &col, &rig) != 2) break;
            init(col, rig);
        }
        else if (strcmp(comando, "toggle_air_route") == 0) {
            int x1, y1, x2, y2;
            if (scanf("%d %d %d %d", &x1, &y1, &x2, &y2) != 4) break;
            toggle_air_route(x1, y1, x2, y2);
        }
        else if (strcmp(comando, "change_cost") == 0) {
            int x1, y1, v, r;
            if (scanf("%d %d %d %d", &x1, &y1, &v, &r) != 4) break;
            change_cost(x1, y1, v, r);
        }
        else if (strcmp(comando, "travel_cost") == 0) {
            int x1, y1, x2, y2;
            if (scanf("%d %d %d %d", &x1, &y1, &x2, &y2) != 4) break;
            int costo_finale = travel_cost(x1, y1, x2, y2);
            printf("%d\n", costo_finale);
        }
    }



    return 0;
}
