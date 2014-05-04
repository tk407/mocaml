#!/bin/bash
for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_sys" "kpn_tramp" "kpn_vm" "kpn_dlcont" "kpn_mcon"
do
 sed - '/n=\(.*\)/ { s/n=\(.*\)\n/\1, /g 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\1/ 
                                                           H} ' ${impl}_data.txt
done 

# kpn
#for size in "1000" "10000" "100000" "1000000" "10000000" "1000000000" "10000000000" "100000000000" "1000000000000" "10000000000000" "100000000000000" "1000000000000000" "10000000000000000" "1000000000000000000" "10000000000000000000" "100000000000000000000"
#do
# for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_sys" "kpn_tramp" "kpn_vm" "kpn_dlcont" "kpn_mcon"
# do
#  printf "n=" >> ${impl}_data.txt
#  printf $size >> ${impl}_data.txt
#  printf " " >> ${impl}_data.txt
#  ./$impl -n $size -q >> ${impl}_data.txt
#  printf "\n" >> ${impl}_data.txt
# done

