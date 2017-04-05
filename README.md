# Verified PAM Cracklib

A verified rewrite of the PAM cracklib module.

## Getting Started

You'll need a fairly particular system setup to compile this project. It's far easier to use [this Vagrant environment](https://github.com/sr-lab/verified-pam-environment) and be assured that it contains everything you need. Alternatively, run [the provisioning script included](https://github.com/sr-lab/verified-pam-environment/blob/master/provision.sh) alongside the Vagrant box on a clean install of Ubuntu 16.04.

### Prerequisites

This project's main dependencies are on Coq and GHC (the Glasgow Haskell Compiler) but several smaller libraries are required including `libpam` and `libcrack2`. The `expect` interactive script automation environment is required to run the evaluation scripts. You'll need:

* Coq v8.6
* GHC
* The following `apt` library packages:
    + `libpam0g-dev`
	+ `libpam-cracklib`
	+ `libcrack2-dev`
* Expect (for evaluation scripts)

Once again, take a look at [the provisioning script included](https://github.com/sr-lab/verified-pam-environment/blob/master/provision.sh) or use [the Vagrant box](https://github.com/sr-lab/verified-pam-environment) if in doubt.

### Installing

Build the module by navigating to the `src` directory and calling `make`. On successful build, type `sudo make install`.


```bash
cd src
make
sudo make install
```

To activate the module (that is, configure your `passwd` utility) to use it, type `sudo make activate`

```bash
sudo make activate
```

This will modify your `/etc/pam.d/common-password` file to use the __verified__ module as the password quality checker during password changes using the `passwd` utility. To switch back to the default `pam_cracklib` implementation, use `sudo make deactivate`.

```bash
sudo make deactivate
```
