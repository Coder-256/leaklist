#!/usr/bin/env bash

MIRIFLAGS=-Zmiri-ignore-leaks cargo +nightly miri run --example demo