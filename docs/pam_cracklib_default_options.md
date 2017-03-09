# Overview
An overview of this module's details is presented below:

* __Module name:__ pam_cracklib
* __Main file:__ pam_cracklib.c

# Configuration
This module takes several options, and contains a structure `cracklib_options` 
designed to hold values for those options in memory (`pam_cracklib.c 94-110`):

```c
struct cracklib_options {
	int retry_times;
	int diff_ok;
	int min_length;
	int dig_credit;
	int up_credit;
	int low_credit;
	int oth_credit;
        int min_class;
	int max_repeat;
	int max_sequence;
        int max_class_repeat;
	int reject_user;
        int gecos_check;
        int enforce_for_root;
        const char *cracklib_dictpath;
};
```

## Defaults
This module contains a set of constants declared with `#define` prefixed with
`CO_` (presumably short for `compiled`). These serve as the default values for
relevant options, with two notable notable exception `CO_MIN_LENGTH_BASE` and
`CO_MIN_WORD_LENGTH` (`pam_cracklib.c 112-120`):

```c
#define CO_RETRY_TIMES  1
#define CO_DIFF_OK      5
#define CO_MIN_LENGTH   9
# define CO_MIN_LENGTH_BASE 5
#define CO_DIG_CREDIT   1
#define CO_UP_CREDIT    1
#define CO_LOW_CREDIT   1
#define CO_OTH_CREDIT   1
#define CO_MIN_WORD_LENGTH 4
```

Additionally, the location of the cracklib dictionaries are defined as `NULL` if
not predefined:

```c
#ifndef CRACKLIB_DICTS
#define CRACKLIB_DICTS NULL
#endif
```

See the table below for mappings beween these constants and option structure
values.

| Constant             | Option        | Default Value   | Notes                                                                                         |
|----------------------|---------------|-----------------|-----------------------------------------------------------------------------------------------|
| `CO_RETRY_TIMES`     | `retry_times` | `1`             | Default value for number of retry attempts.                                                   |
| `CO_DIFF_OK`         | `diff_ok`     | `5`             | Default value for minimum acceptable distance.                                                |
| `CO_MIN_LENGTH`      | `min_length`  | `9`             | Default value for minimum length.                                                             |
| `CO_MIN_LENGTH_BASE` | `min_length`  | `5`             | Hard lower limit on minimum length. Cannot be overridden by configuration.                    |
| `CO_DIG_CREDIT`      | `dig_credit`  | `1`             | Default value for digit character credits.                                                    |
| `CO_LOW_CREDIT`      | `low_credit`  | `1`             | Default value for lowercase character credits.                                                |
| `CO_UP_CREDIT`       | `up_credit`   | `1`             | Default value for uppercase character credits.                                                |
| `CO_OTH_CREDIT`      | `oth_credit`  | `1`             | Default value for other character credits.                                                    |
| `CO_MIN_WORD_LENGTH` | `N/A`         | `4`             | Lower limit on word length that, if present in the GECOS file, will cause password rejection. |

There are a number of other options that are not set by default:

| Option              | Default           | Effect                                                                                                            |
|---------------------|-------------------|-------------------------------------------------------------------------------------------------------------------|
| `min_class`         | `0`               | Minimum number of character classes check disabled.                                                               |
| `max_repeat`        | `0`               | Maximum number of character repetitions check disabled.                                                           |
| `max_sequence`      | `0`               | Maximum number of ascending/descending character sequences check disabled.                                        |
| `max_class_repeat`  | `0`               | Maximum number of consecutive characters of the same class check disabled.                                        |
| `reject_user`       | `0`               | Password will not be rejected if identical to the username.                                                       |
| `gecos_check`       | `0`               | Password containing GECOS entries will not be rejected.                                                           |
| `enforce_for_root`  | `0`               | Password check will not be enforced for root.                                                                     |
| `cracklib_dictpath` | `NULL/Predefined` | Will default to the value of the `CRACKLIB_DICTS` constant. Points to location of dictionaries file for cracklib. |

## Initialisation
These values are initialised in the code (`pam_cracklib.c 739-747`):

```c
memset(&options, 0, sizeof(options));
options.retry_times = CO_RETRY_TIMES;
options.diff_ok = CO_DIFF_OK;
options.min_length = CO_MIN_LENGTH;
options.dig_credit = CO_DIG_CREDIT;
options.up_credit = CO_UP_CREDIT;
options.low_credit = CO_LOW_CREDIT;
options.oth_credit = CO_OTH_CREDIT;
options.cracklib_dictpath = CRACKLIB_DICTS;
```
