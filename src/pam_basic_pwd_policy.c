/*
 * Software Reliability Lab: Password Quality PAM Module 
 * (Based on pam_cracklib)
 */

#include "config.h"

#include <stdio.h>
#ifdef HAVE_LIBXCRYPT
#include <xcrypt.h>
#elif defined(HAVE_CRYPT_H)
#include <crypt.h>
#endif
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <ctype.h>
#include <limits.h>
#include <pwd.h>
#include <security/pam_modutil.h>

#ifndef CRACKLIB_DICTS
#define CRACKLIB_DICTS NULL
#endif


/* For Translators: "%s%s" could be replaced with "<service> " or "". */
#define PROMPT1 _("New %s%spassword: ")
/* For Translators: "%s%s" could be replaced with "<service> " or "". */
#define PROMPT2 _("Retype new %s%spassword: ")
#define MISTYPED_PASS _("Sorry, passwords do not match.")

#ifdef MIN
#undef MIN
#endif
#define MIN(_a, _b) (((_a) < (_b)) ? (_a) : (_b))

// JFF
/* Haskell FFI */
#include <HsFFI.h>
#ifdef __GLASGOW_HASKELL__
#include "PamInterface_stub.h"
extern void __stginit_PamInterface (void);
#endif

/*
 * here, we make a definition for the externally accessible function
 * in this file (this definition is required for static a module
 * but strongly encouraged generally) it is used to instruct the
 * modules include file to define the function prototypes.
 */

#define PAM_SM_PASSWORD

#include <security/pam_modules.h>
#include <security/_pam_macros.h>
#include <security/pam_ext.h>

/* argument parsing */
#define PAM_DEBUG_ARG       0x0001

struct cracklib_options
{
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

#define CO_RETRY_TIMES  1
#define CO_DIFF_OK      5
#define CO_MIN_LENGTH   9
#define CO_MIN_LENGTH_BASE 5
#define CO_DIG_CREDIT   1
#define CO_UP_CREDIT    1
#define CO_LOW_CREDIT   1
#define CO_OTH_CREDIT   1
#define CO_MIN_WORD_LENGTH 4

static int
_pam_parse (pam_handle_t * pamh, struct cracklib_options *opt,
	    int argc, const char **argv)
{
  int ctrl = 0;

  /* step through arguments */
  for (ctrl = 0; argc-- > 0; ++argv)
    {
      char *ep = NULL;

      /* generic options */

      if (!strcmp (*argv, "debug"))
	ctrl |= PAM_DEBUG_ARG;
      else if (!strncmp (*argv, "type=", 5))
	pam_set_item (pamh, PAM_AUTHTOK_TYPE, *argv + 5);
      else if (!strncmp (*argv, "retry=", 6))
	{
	  opt->retry_times = strtol (*argv + 6, &ep, 10);
	  if (!ep || (opt->retry_times < 1))
	    opt->retry_times = CO_RETRY_TIMES;
	}
      else if (!strncmp (*argv, "difok=", 6))
	{
	  opt->diff_ok = strtol (*argv + 6, &ep, 10);
	  if (!ep || (opt->diff_ok < 0))
	    opt->diff_ok = CO_DIFF_OK;
	}
      else if (!strncmp (*argv, "difignore=", 10))
	{
	  /* just ignore */
	}
      else if (!strncmp (*argv, "minlen=", 7))
	{
	  opt->min_length = strtol (*argv + 7, &ep, 10);
	  if (!ep || (opt->min_length < CO_MIN_LENGTH_BASE))
	    opt->min_length = CO_MIN_LENGTH_BASE;
	}
      else if (!strncmp (*argv, "dcredit=", 8))
	{
	  opt->dig_credit = strtol (*argv + 8, &ep, 10);
	  if (!ep)
	    opt->dig_credit = 0;
	}
      else if (!strncmp (*argv, "ucredit=", 8))
	{
	  opt->up_credit = strtol (*argv + 8, &ep, 10);
	  if (!ep)
	    opt->up_credit = 0;
	}
      else if (!strncmp (*argv, "lcredit=", 8))
	{
	  opt->low_credit = strtol (*argv + 8, &ep, 10);
	  if (!ep)
	    opt->low_credit = 0;
	}
      else if (!strncmp (*argv, "ocredit=", 8))
	{
	  opt->oth_credit = strtol (*argv + 8, &ep, 10);
	  if (!ep)
	    opt->oth_credit = 0;
	}
      else if (!strncmp (*argv, "minclass=", 9))
	{
	  opt->min_class = strtol (*argv + 9, &ep, 10);
	  if (!ep)
	    opt->min_class = 0;
	  if (opt->min_class > 4)
	    opt->min_class = 4;
	}
      else if (!strncmp (*argv, "maxrepeat=", 10))
	{
	  opt->max_repeat = strtol (*argv + 10, &ep, 10);
	  if (!ep)
	    opt->max_repeat = 0;
	}
      else if (!strncmp (*argv, "maxsequence=", 12))
	{
	  opt->max_sequence = strtol (*argv + 12, &ep, 10);
	  if (!ep)
	    opt->max_sequence = 0;
	}
      else if (!strncmp (*argv, "maxclassrepeat=", 15))
	{
	  opt->max_class_repeat = strtol (*argv + 15, &ep, 10);
	  if (!ep)
	    opt->max_class_repeat = 0;
	}
      else if (!strncmp (*argv, "reject_username", 15))
	{
	  opt->reject_user = 1;
	}
      else if (!strncmp (*argv, "gecoscheck", 10))
	{
	  opt->gecos_check = 1;
	}
      else if (!strncmp (*argv, "enforce_for_root", 16))
	{
	  opt->enforce_for_root = 1;
	}
      else if (!strncmp (*argv, "authtok_type", 12))
	{
	  /* for pam_get_authtok, ignore */ ;
	}
      else if (!strncmp (*argv, "use_authtok", 11))
	{
	  /* for pam_get_authtok, ignore */ ;
	}
      else if (!strncmp (*argv, "use_first_pass", 14))
	{
	  /* for pam_get_authtok, ignore */ ;
	}
      else if (!strncmp (*argv, "try_first_pass", 14))
	{
	  /* for pam_get_authtok, ignore */ ;
	}
      else if (!strncmp (*argv, "dictpath=", 9))
	{
	  opt->cracklib_dictpath = *argv + 9;
	  if (!*(opt->cracklib_dictpath))
	    {
	      opt->cracklib_dictpath = CRACKLIB_DICTS;
	    }
	}
      else
	{
	  pam_syslog (pamh, LOG_ERR, "pam_parse: unknown option; %s", *argv);
	}
    }

  return ctrl;
}

static int
_pam_unix_approve_pass (pam_handle_t * pamh,
			unsigned int ctrl,
			struct cracklib_options *opt,
			const char *pass_old, const char *pass_new)
{
  const char *msg = NULL;
  const char *user;
  int retval;

  // JFF: we do not want to check if they are the same here
  //if (pass_new == NULL || (pass_old && !strcmp(pass_old,pass_new))) {
  if (pass_new == NULL)
    {
      if (ctrl & PAM_DEBUG_ARG)
	pam_syslog (pamh, LOG_DEBUG, "bad authentication token");
      pam_error (pamh, "%s", pass_new == NULL ?
		 _("No password supplied") : _("Password unchanged"));
      return PAM_AUTHTOK_ERR;
    }

  retval = pam_get_user (pamh, &user, NULL);
  if (retval != PAM_SUCCESS || user == NULL)
    {
      if (ctrl & PAM_DEBUG_ARG)
	pam_syslog (pamh, LOG_ERR, "Can not get username");
      return PAM_AUTHTOK_ERR;
    }

  // JFF
  /* Check if the password transition satisfies the synthesised password policy */
  char *oldPwd = pass_old;
  char *newPwd = pass_new;
  char *s = main_check_hs (oldPwd, newPwd);
  if (s && strlen (s) > 0)
    {
      /* If there are error messages, report them to the user. */
      msg = _(s);
    }

  if (msg)
    {
      if (ctrl & PAM_DEBUG_ARG)
	pam_syslog (pamh, LOG_NOTICE,
		    "new passwd fails strength check: %s", msg);
      pam_error (pamh, _("BAD PASSWORD: %s"), msg);
      return PAM_AUTHTOK_ERR;
    };
  return PAM_SUCCESS;

}

/* The Main Thing (by Cristian Gafton, CEO at this module :-)
 * (stolen from http://home.netscape.com)
 */
int
pam_sm_chauthtok (pam_handle_t * pamh, int flags, int argc, const char **argv)
{
  /* Initialize Haskell runtime. */
  hs_init (NULL, NULL);
#ifdef __GLASGOW_HASKELL__
  hs_add_root (__stginit_PamInterface);
#endif

  unsigned int ctrl;
  struct cracklib_options options;

  D (("called."));

  memset (&options, 0, sizeof (options));
  options.retry_times = CO_RETRY_TIMES;
  options.diff_ok = CO_DIFF_OK;
  options.min_length = CO_MIN_LENGTH;
  options.dig_credit = CO_DIG_CREDIT;
  options.up_credit = CO_UP_CREDIT;
  options.low_credit = CO_LOW_CREDIT;
  options.oth_credit = CO_OTH_CREDIT;
  options.cracklib_dictpath = CRACKLIB_DICTS;

  ctrl = _pam_parse (pamh, &options, argc, argv);

  if (flags & PAM_PRELIM_CHECK)
    {
      /* Check for passwd dictionary */
      /* We cannot do that, since the original path is compiled
         into the cracklib library and we don't know it.  */
      return PAM_SUCCESS;
    }
  else if (flags & PAM_UPDATE_AUTHTOK)
    {
      int retval;
      const void *oldtoken;
      int tries;

      D (("do update"));

      retval = pam_get_item (pamh, PAM_OLDAUTHTOK, &oldtoken);
      if (retval != PAM_SUCCESS)
	{
	  if (ctrl & PAM_DEBUG_ARG)
	    pam_syslog (pamh, LOG_ERR, "Can not get old passwd");
	  oldtoken = NULL;
	}

      tries = 0;
      while (tries < options.retry_times)
	{
	  const char *crack_msg;
	  const char *newtoken = NULL;


	  tries++;

	  /* Planned modus operandi:
	   * Get a passwd.
	   * Verify it against cracklib.
	   * If okay get it a second time.
	   * Check to be the same with the first one.
	   * set PAM_AUTHTOK and return
	   */

	  retval = pam_get_authtok_noverify (pamh, &newtoken, NULL);
	  if (retval != PAM_SUCCESS)
	    {
	      pam_syslog (pamh, LOG_ERR,
			  "pam_get_authtok_noverify returned error: %s",
			  pam_strerror (pamh, retval));
	      continue;
	    }
	  else if (newtoken == NULL)
	    {			/* user aborted password change, quit */
	      return PAM_AUTHTOK_ERR;
	    }

	  /* check it for strength too... */
	  D (("for strength"));
	  // JFF
	  retval = _pam_unix_approve_pass (pamh, ctrl, &options,
					   oldtoken, newtoken);
	  if (retval != PAM_SUCCESS)
	    {
	      if (getuid () || options.enforce_for_root
		  || (flags & PAM_CHANGE_EXPIRED_AUTHTOK))
		{
		  pam_set_item (pamh, PAM_AUTHTOK, NULL);
		  retval = PAM_AUTHTOK_ERR;
		  continue;
		}
	    }

	  retval = pam_get_authtok_verify (pamh, &newtoken, NULL);
	  if (retval != PAM_SUCCESS)
	    {
	      pam_syslog (pamh, LOG_ERR,
			  "pam_get_authtok_verify returned error: %s",
			  pam_strerror (pamh, retval));
	      pam_set_item (pamh, PAM_AUTHTOK, NULL);
	      continue;
	    }
	  else if (newtoken == NULL)
	    {			/* user aborted password change, quit */
	      return PAM_AUTHTOK_ERR;
	    }

	  return PAM_SUCCESS;
	}

      D (("returning because maxtries reached"));

      pam_set_item (pamh, PAM_AUTHTOK, NULL);

      /* if we have only one try, we can use the real reason,
         else say that there were too many tries. */
      if (options.retry_times > 1)
	return PAM_MAXTRIES;
      else
	return retval;

    }
  else
    {
      if (ctrl & PAM_DEBUG_ARG)
	pam_syslog (pamh, LOG_NOTICE, "UNKNOWN flags setting %02X", flags);
      return PAM_SERVICE_ERR;
    }

  hs_exit ();			/* Finished with Haskell runtime. */

  /* Not reached */
  return PAM_SERVICE_ERR;
}
