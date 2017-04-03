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
