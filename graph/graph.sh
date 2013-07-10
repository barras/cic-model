#!/bin/bash

## Utils

copyarray () {
  string=$(declare -p $1)
  eval "local -A tmp="${string#*=}
  for i in ${!tmp[*]} ; do
    eval "$2[$i]=\"${tmp[$i]}\""
  done
}

## Sets

setof () {
  declare -A set
  for i in $* ; do
    set[$i]=1
  done
  echo ${!set[*]}
}

diffset () {
  declare -A set1 set2
  read l1
  read l2
#N=`echo $l1 | wc -w`
  for i in $l2 ; do
    set2[$i]=1
  done
  for i in $l1 ; do
    if [ -z "${set2[$i]}" ] ; then
      set1[$i]=1
    fi
  done
#echo "$N - ${#set2[*]} = ${#set1[*]}" > /dev/stderr
  echo ${!set1[*]}
}

## Graphs

# readgr () {
#   declare 
#   while read x l ; do
#     echo "[$x]=\"$l\" "
#   done
# }

trclos () {
  unset src dest
  declare -A src dest seen
  copyarray $1 src

  rec () {
    if [ -z "${seen[$1]}" ] ; then
      seen[$1]=1
      chld=`for i in ${src[$1]} ; do
        rec $i ; echo ${src[$i]} ${dest[$i]}
      done`
      dest[$1]="`setof $chld`"      
    fi
  }
  for i in ${!src[*]} ; do
    rec $i > /dev/null
#    time rec $i > /dev/null
  done
declare -p dest > /tmp/dest.g
  copyarray dest $2
}


trdiff () {
  unset tmp1 tmp2
  declare -A tmp1 tmp2
  copyarray $1 tmp1
  copyarray $2 tmp2

  for i in ${!tmp1[*]} ; do
#    l=""
#    for j in ${tmp2}
    tmp1[$i]=`echo -e "${tmp1[$i]}\n${tmp2[$i]}"|diffset`
  done

  copyarray tmp1 $1

}


writedot () {
  declare -A tmpw
  copyarray $1 tmpw

  echo "strict digraph CicModel {"
#  echo "  size=\"1000,1000\";"
#  echo "  rankdir=LR;"
#  echo "  ratio=;"
  echo "  node [shape=egg,style=filled,fillcolor=\"#ff8080\",target=\"CicModel\"];"
  echo "  edge [weight=10];"
#  for i in ${!tmpw[*]} ; do  
#    echo "  $i [href=\"../html/\N.html\"];"
#  done
  for i in ${!tmpw[*]} ; do  
    for j in ${tmpw[$i]} ; do  
      echo "  $i -> $j;"
    done
  done
  echo "}"
}

## Dependencies

declare -A deps acc
export deps acc

lib2graph () {

while read l ; do
  l=`basename $l .html`
  deps[$l]="<>"
done

process () {
  case "$1" in
    ""|\#*)
     return ;;
    *.vo)
      l=`basename $1 .vo` ;;
    *.vo:)
      l=`basename $1 .vo:` ;;
    *)
      return ;;
  esac
#  if [ ! "${deps[$l]}" == "<>" ] ; then return ; fi

  while true ; do
    case "$1" in
      ""|*:)
        shift
        break;;
    esac
    shift
  done

  nodes=""
  while true ; do
    case "$1" in
      "")
        break ;;
      *.vo)
        nodes="$nodes `basename $1 .vo`"
        ;;
    esac
    shift
  done
  deps[$l]=`setof $nodes`
}
while read l ; do process $l ; done < .depend
NODES=${#deps[*]}
EDGES=`echo ${deps[*]} | wc -w`
echo -e "Nodes: $NODES\tEdges: $EDGES" > /dev/stderr

#echo "* Begin trclos" > /dev/stderr
#time trclos deps acc > /dev/stderr

#declare -p deps acc
writedot deps
}


graph2dot () {
  g=$1
  if [ ! -f "$g" ] ; then
    echo "*** Graph file \"$g\" not found"
    exit 1
  fi
  source $1

#declare -p deps
N1=`echo ${deps[*]} | wc -w`
N2=`echo ${acc[*]} | wc -w`
echo "* Begin trdiff" > /devstderr
trdiff deps acc
echo "* End trdiff" > /dev/stderr
N3=`echo ${deps[*]} | wc -w`
echo
#declare -p acc
#declare -p deps
#echo
echo $N1 $N2 $N3 > /dev/stderr

writedot deps

}
#cat deps.dot

$*
