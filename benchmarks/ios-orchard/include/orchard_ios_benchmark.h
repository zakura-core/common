#ifndef ORCHARD_IOS_BENCHMARK_H
#define ORCHARD_IOS_BENCHMARK_H

#include <stddef.h>

char *orchard_ios_benchmark_run(
    const char *hardware_identifier,
    const char *model,
    const char *soc,
    const char *os_version,
    const char *thermal_state_start,
    size_t active_processor_count
);

void orchard_ios_benchmark_string_free(char *value);

#endif
