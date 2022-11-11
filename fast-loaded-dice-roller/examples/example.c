/*
  Name:     example.c
  Purpose:  Example of running FLDR.
  Author:   F. A. Saad
  Copyright (C) 2020 Feras A. Saad, All Rights Reserved.

  Released under Apache 2.0; refer to LICENSE.txt
*/

#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include "fldr.h"
#include "flip.h"

// Struct for sample records.
typedef struct record {
  int sample; // sample value
  int bits;   // number of random bits used to obtain the sample
} record;

int main(int argc, char **argv) {
  long start, end;
  struct timeval timecheck;

  gettimeofday(&timecheck, NULL);
  start = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  int N = 200;
  int N_sample = 100000;
  int *samples = calloc(N_sample, sizeof(*samples));
  record records[N_sample];

  // Uniform distribution.
  int distribution[N];
  for (int i = 0; i < N; i++) {
    distribution[i] = 1;
  }

  fldr_preprocess_t *x = fldr_preprocess(distribution, N);

  gettimeofday(&timecheck, NULL);
  end = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  printf("setup: %ld milliseconds elapsed\n", (end - start));

  gettimeofday(&timecheck, NULL);
  start = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  // Generate samples
  for (int i = 0; i < N_sample; i++) {
    samples[i] = fldr_sample(x);
    /* printf("%d ", samples[i]); */
    
    // Build sample record.
    records[i] = (record){ .sample = samples[i], .bits = num_bits };
    // Reset bit counter.
    num_bits = 0;
  }
  printf("\n");

  gettimeofday(&timecheck, NULL);
  end = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

  printf("sample: %ld milliseconds elapsed\n", (end - start));

  free(samples);
  fldr_free(x);
  
  // Dump records to file.
  FILE *fd = fopen("fldr_c_samples.dat", "w");
  for (int i = 0; i < N_sample; i++) {
    fprintf(fd, "%d %d\n", records[i].sample, records[i].bits);
  }
  fclose(fd);
}
