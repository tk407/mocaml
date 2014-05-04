#!/bin/bash
#clean-up
for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm" "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 rm -f ${impl}_data.txt
 rm -f ${impl}_data_clean.txt
done 

echo 'KPN tests'

# kpn
for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm" "kpn_mcon" "kpn_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "1000" "10000" "100000" "1000000" "10000000" "100000000" "1000000000" "10000000000" "100000000000" "1000000000000" "10000000000000" "100000000000000" "1000000000000000" "10000000000000000" "100000000000000000" "1000000000000000000" "10000000000000000000" "100000000000000000000" "1000000000000000000000"
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done
done

echo 'Sieve tests'

# sieve
for impl in "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sieve_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "3" "4" "6" "8" "10" "12" "14" "16" "18" "20" "22" "24" "26" "28" "30" "32" "34" "36" "38" "40" "44" "48" "50"
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done
done
 
echo 'Concurrent sort tests'

# sorter
for impl in "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon" "sorter_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "3" "4" "6" "8" "10" "12" "14" "16" "18" "20" "22" "24" "26" "28" "30" "32" "34" "36" "38" "40" "44" "48" "50"
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done 
done

echo 'Tests done!'
echo 'File transforms'

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm" "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed -i '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt
done 

#user time

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\1/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_usertime.txt
done 

#system time

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\2/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_systime.txt
done 

#real time

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\3/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_realtime.txt
done 

#memory

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\4/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_mem.txt
done 
