#!/bin/bash
#clean-up
for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm" "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_mcon_ftt" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 rm -f ${impl}_data.txt
 rm -f ${impl}_data_clean.txt
 rm -f ${impl}_data_clean_usertime.txt
 rm -f ${impl}_data_clean_realtime.txt
 rm -f ${impl}_data_clean_systime.txt
 rm -f ${impl}_data_clean_mem.txt
done 

echo 'KPN tests'

make kpn.bc

# kpn
for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm" "kpn_mcon" "kpn_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "1000" "10000" "100000" "1000000" "10000000" "100000000" "1000000000" "10000000000" "100000000000" "1000000000000" "10000000000000" "100000000000000" "1000000000000000" "10000000000000000" "100000000000000000" "1000000000000000000" "10000000000000000000" "100000000000000000000" "1000000000000000000000" "10000000000000000000000" "100000000000000000000000"
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done
done

echo 'Sieve tests'

make sieve.bc

# sieve
for impl in "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sieve_mcon_ftt" "sieve_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "3" "4" "6" "8" "10" "12" "14" "16" "18" "20" "22" "24" "26" "28" "30" "32" "34" "36" "38" "40" "44" "48" "50" "55" "60"
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done
done
 

#sieve extension

for impl in "sieve_cont" "sieve_sys" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon_ftt" "sieve_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "70" "80" "90" "100" "120" "140" "160" "180" "200"
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done
done

echo 'Concurrent sort tests'



make sorter.bc

# sorter
for impl in "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon" "sorter_lwt"
do
 printf "Testing: "
 echo $impl
 for size in "3" "4" "6" "8" "10" "12" "14" "16" "18" "20" "22" "24" "26" "28" "30" "32" "34" "36" "38" "40" "44" "48" "50" "52" "54" "56" "58" "60" "62" "64" "66" "68" "70" "75" "80" "85" "90" "95" "100" "110" "120" "130" "140" "150" "160" "180" "190" "200" "210" "220" "230" "240" "250" "260" "280" "290" "300" 
 do
  printf "n=" >> ${impl}_data.txt
  printf $size >> ${impl}_data.txt
  printf " " >> ${impl}_data.txt
  ./$impl -n $size -q >> ${impl}_data.txt
  printf "\n" >> ${impl}_data.txt
 done 
done

# sorter extension

for impl in "sorter_cont" "sorter_promise" "sorter_tramp" "sorter_mcon" "sorter_sys"
do
 printf "Testing: "
 echo $impl
 for size in  "320" "340" "360" "380" "400" "450" "500" "550"
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

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm" "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_mcon_ftt" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed -i '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt
done 

#user time

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_mcon_ftt" "sieve_promise" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\1/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_usertime.txt
done 

#system time

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_mcon_ftt" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\2/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_systime.txt
done 

#real time

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_mcon_ftt" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\3/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_realtime.txt
done 

#memory

for impl in "kpn_cont" "kpn_sys" "kpn_promise" "kpn_tramp" "kpn_vm"  "kpn_mcon" "sieve_cont" "sieve_sys" "sieve_promise" "sieve_mcon_ftt" "sieve_tramp" "sieve_vm" "sieve_mcon" "sorter_cont" "sorter_sys" "sorter_promise" "sorter_tramp" "sorter_vm" "sorter_mcon"
do
 sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' ${impl}_data.txt | sed -n '/n=\(.*\)/ { s/n=\(.*\)/\1/ 
                      x
                      p }
         /user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/ { s/user \(.*\) sys \(.*\) real \(.*\) mem \(.*\)/\4/ 
                                                           H} ' | sed '/^[[:space:]]*$/d;s/[[:space:]]*$//' | sed 'N;s/\n/, /' > ${impl}_data_clean_mem.txt
done 
