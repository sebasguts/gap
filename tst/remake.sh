#! /bin/sh 
input0=/tmp/gapinput0.$$
input=/tmp/gapinput.$$
logfile=/tmp/gaplog.$$
prelogfile=/tmp/gapprelog.$$
sedscript=/tmp/sedfile.$$
cat > $sedscript <<EOF
/^#/ p
/^$/ p
/^ \+$/ p
/^\(gap\)\?> /  !d
s/^\(gap\)\?> //
EOF
sed  -f $sedscript < $1 > $input0
cat - $input0 > $input <<EOF
LogTo("$prelogfile");
EOF
cat $input - > $input0 <<EOF
LogTo();
quit;
EOF
../bin/gap.sh -N  -x 80 -r < $input0 > /dev/null
cat > $sedscript <<EOF
s/^gap> #/#/
s/^gap> \+$//
/^\$Id: / d
/^GAP4stones: / d
/^gap> LogTo();/ d
EOF
sed -f $sedscript < $prelogfile > $logfile
echo result in $logfile
