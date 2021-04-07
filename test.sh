#!/bin/bash

racket test.rkt

racket run.rkt > generated.txt
diff generated.txt output.txt
rm generated.txt
