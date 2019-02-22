DUMP="."

if [ "$1" != "" ]; then
  DUMP=$1
fi

echo "Auto classified (a):  `grep '^^^^' $DUMP/dump-good.txt | wc -l`"
echo "Auto classified (c):  `grep '^^^^' $DUMP/dump-etc.txt | wc -l`"
echo "Not fixed / finished: `grep '^^^^' $DUMP/dump-nothing.txt | wc -l`"
echo "Manually processed:   `cat $DUMP/dump-what.txt | wc -l`"

