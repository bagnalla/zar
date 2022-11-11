// Main harness for C samplers.
// ** @author: fsaad@mit.edu

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>

#include "flip.h"
#include "readio.h"
#include "sample.h"
#include "sstructs.h"

#include "macros.c"

// Struct for sample records.
typedef struct record {
  int sample; // sample value
  int bits;   // number of random bits used to obtain the sample
} record;

int main(int argc, char **argv) {
  // Read command line arguments.
  if (argc != 5) {
    printf("usage: ./mainc seed steps sampler path\n");
    exit(0);
  }
  int seed = atoi(argv[1]);
  int steps = atoi(argv[2]);
  char *sampler = argv[3];
  char *path = argv[4];

  printf("%d %d %s %s\n", seed, steps, sampler, path);
  srand(seed);

  long start, end;
  struct timeval timecheck;

  gettimeofday(&timecheck, NULL);
  start = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  /* int x = 0; */
  /* clock_t t; */
  /* READ_SAMPLE_TIME("ky.enc", */
  /*     sampler, */
  /*     sample_ky_encoding_s, */
  /*     read_sample_ky_encoding, */
  /*     sample_ky_encoding, */
  /*     free_sample_ky_encoding_s, */
  /*     path, steps, t, x) */
  /* else READ_SAMPLE_TIME("ky.mat", */
  /*     sampler, */
  /*     sample_ky_matrix_s, */
  /*     read_sample_ky_matrix, */
  /*     sample_ky_matrix, */
  /*     free_sample_ky_matrix_s, */
  /*     path, steps, t, x) */
  /* else READ_SAMPLE_TIME("ky.matc", */
  /*     sampler, */
  /*     sample_ky_matrix_cached_s, */
  /*     read_sample_ky_matrix_cached, */
  /*     sample_ky_matrix_cached, */
  /*     free_sample_ky_matrix_cached_s, */
  /*     path, steps, t, x) */
  /* else { */
  /*     printf("Unknown sampler: %s\n", sampler); */
  /*     exit(1); */
  /* } */

  struct sample_ky_encoding_s s = read_sample_ky_encoding(path);

  gettimeofday(&timecheck, NULL);
  end = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  printf("setup: %ld milliseconds elapsed\n", (end - start));

  record records[steps];
  FILE *fd = fopen("optas_c_samples.dat", "w");

  gettimeofday(&timecheck, NULL);
  start = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  for (int i = 0; i < steps; i++) {
    int sample = sample_ky_encoding(&s);
    /* printf("%d\n", sample); */
    fprintf(fd, "%d %d\n", sample - 1, num_bits);
    num_bits = 0;
  }

  gettimeofday(&timecheck, NULL);
  end = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  printf("sample: %ld milliseconds elapsed\n", (end - start));

  fclose(fd);
  /* double e = ((double)t) / CLOCKS_PER_SEC; */
  /* printf("%s %1.5f %ld\n", sampler, e, NUM_RNG_CALLS); */

  return 0;
}
