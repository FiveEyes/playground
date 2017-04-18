//Hanzhong Xu and Meng Meng

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

char *kos_doc = "docword.kos.txt";
char *kos_voc = "vocab.kos.txt";

char *nips_doc = "docword.nips.txt";
char *nips_voc = "vocab.nips.txt";

#define MAX_INPUT_SIZE 1000000
#define MAX_DOC_NUM 3500
#define MAX_VOCAB_NUM 13000
#define MAX_WORDS 2000000
#define MAX_TOPIC_NUM 10

int DN, WN, LN, K;

int lines[MAX_INPUT_SIZE][3];
char * vocab[MAX_VOCAB_NUM];

int Wnd[MAX_WORDS], doc_idx[MAX_DOC_NUM], Wnd_size;

int Znd[MAX_WORDS];                     // the words' topic
int Cwk[MAX_VOCAB_NUM][MAX_TOPIC_NUM];  // # of times word w is assigned to topic k
int Ck[MAX_TOPIC_NUM];                  // # of words assigned to topic k
int Cdk[MAX_DOC_NUM][MAX_TOPIC_NUM];    // # of words from topic k in document d
#define Cd(i) (doc_idx[i+1]-doc_idx[i]) // # of words in doc d
double alpha = 1.0, beta = 1.0;
double phi[MAX_VOCAB_NUM][MAX_TOPIC_NUM], theta[MAX_DOC_NUM][MAX_TOPIC_NUM];

void readfile(char * doc_fn, char * voc_fn) {
  FILE * fin;
  
  fin = fopen(doc_fn, "r");
	fscanf(fin, "%d%d%d", &DN, &WN, &LN);
	for(int i = 0; i < LN; ++i) {
		fscanf(fin, "%d%d%d", lines[i], lines[i] + 1, lines[i] + 2);
		lines[i][0]--; lines[i][1]--;
	}
	fclose(fin);
	
	fin = fopen(voc_fn, "r");
	static char s[100];
	
	for(int i = 0; i < WN; ++i) {
	  fscanf(fin, "%s", s);
	  int len = strlen(s);
	  vocab[i] = (char *)malloc((len + 1) * sizeof(char));
	  strcpy(vocab[i], s);
	  //puts(s);
  }
  fclose(fin);
}

void init_Wnd() {
  Wnd_size = 0;
  for(int i = 0; i < LN; ++i) {
    if(i == 0 || lines[i][0] != lines[i - 1][0]) {
      doc_idx[lines[i][0]] = Wnd_size;
    }
    for(int j = 0; j < lines[i][2]; ++j) {
      Wnd[Wnd_size++] = lines[i][1];
    }
  }
  doc_idx[DN] = Wnd_size;
  //printf("%d %d\n", doc_idx[DN-1], doc_idx[DN]);
  //getchar();
}

void init_ZC() {
  memset(Znd, 0, sizeof(Znd));
  memset(Cwk, 0, sizeof(Cwk));
  memset(Ck, 0, sizeof(Ck));
  memset(Cdk, 0, sizeof(Cdk));
  memset(phi, 0, sizeof(phi));
  memset(theta, 0, sizeof(theta));
}

void init_sampling() {
  for(int i = 0; i < DN; ++i) {
    for(int j = doc_idx[i]; j < doc_idx[i + 1]; ++j) {
      int k = rand() % K;
      Znd[j] = k;
      Cwk[Wnd[j]][k]++;
      Ck[k]++;
      Cdk[i][k]++;
    }
  }
}

void init(int k) {
  K = k;
  init_Wnd();
  init_ZC();
  init_sampling();
}

double rand_double() {
  return (double)rand() / (double)RAND_MAX;
}

int sample(int d, int n) {
  double p[MAX_TOPIC_NUM], sum = 0.0;
  for(int k = 0; k < K; ++k) {
    //p[k] = WN * 1.0 / (Ck[k] + WN * beta) * (Cwk[Wnd[n]][k] + beta);
    p[k] = 1.0 / (Ck[k] + WN * beta) * (Cwk[Wnd[n]][k] + beta);
    p[k] *= (Cdk[d][k] + alpha) / ((Cd(d) - 1) + K * alpha);
    sum += p[k];
    //printf("p %lf %d %d %d %d\n", p[k], Cwk[Wnd[n]][k], Ck[k], Cdk[d][k], Cd(d));
  }
  //printf("sum %lf\n", sum);
  for(int k = 0; k < K; ++k) {
    p[k] /= sum;
    //printf("p %d %lf\n", k, p[k]);
  }
  
  double r = rand_double();
  //printf("%lf\n", r);
  double tmp = 0.0;
  for(int k = 0; k < K; ++k) {
    tmp += p[k];
    if(r <= tmp) return k;
  }
  return K - 1;
}

void gibbs_sampling(int t) {
  while(t--) {
    printf("t = %d\n", t);
    for(int i = 0; i < DN; ++i) {
      for(int j = doc_idx[i]; j < doc_idx[i + 1]; ++j) {
        int k = Znd[j];
        
        Cwk[Wnd[j]][k]--;
        Ck[k]--;
        Cdk[i][k]--;
        
        k = sample(i, j);
        
        Znd[j] = k;
        Cwk[Wnd[j]][k]++;
        Ck[k]++;
        Cdk[i][k]++;
      }
    }
  }
}

void compute_theta_phi() {
  double chk;
  for(int i = 0; i < WN; ++i) {
    for(int j = 0; j < K; ++j) {
      phi[i][j] = (Cwk[i][j] + beta) / (Ck[j] + WN * beta);
    }
  }
  /*
  for(int j = 0; j < K; ++j) {
    chk = 0.0;
    for(int i = 0; i < WN; ++i) chk += phi[i][j];
    printf("phi_chk %d %lf\n", j, chk);
  }
  */
  for(int i = 0; i < DN; ++i) {
    //chk = 0.0;
    for(int j = 0; j < K; ++j) {
      theta[i][j] = (Cdk[i][j] + alpha) / (Cd(i) + K * alpha);
      //chk += theta[i][j];
    }
    //printf("theta_chk %d %lf\n", i, chk);
  }
}

int word_idx[MAX_VOCAB_NUM], which_topic;

typedef int (*CMP)(const void *, const void*);
int cmp(int *a, int *b) {
  if(phi[(*a)][which_topic] > phi[(*b)][which_topic]) return -1;
  if(phi[(*a)][which_topic] < phi[(*b)][which_topic]) return 1;
  return 0;
}

void sort(int k) {
  which_topic = k;
  for(int i = 0; i < WN; ++i) word_idx[i] = i;
  qsort(word_idx, WN, sizeof(int), (CMP)cmp);
}

void output(int k) {
  sort(k);
  puts("-----------------");
  printf("topic %d\n", k);
  for(int i = 0; i < 10; ++i) printf("%10s\t%lf\n", vocab[word_idx[i]], phi[word_idx[i]][k]);
  puts("-----------------");
}

int main() {
  int K = 2, times = 100;
  srand(time(NULL));
  readfile(kos_doc, kos_voc);
  //readfile(nips_doc, nips_voc);
  
  init(K);
  gibbs_sampling(times);
  
  compute_theta_phi();
  printf("%s K=%d\n", nips_doc, K);
  for(int i = 0; i < K; ++i) output(i);
  return 0;
}
