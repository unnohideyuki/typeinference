#!/bin/sh
i=0

for t in test/*.hs; do
    runhaskell -Wall -i. $t
    if [ $? -ne 0 ]; then
      exit 1
    fi
    i=`expr $i \+ 1`
done

echo "=================="
echo "Finished $i tests."
echo "=================="
