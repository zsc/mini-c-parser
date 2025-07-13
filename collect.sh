dune build
dune exec bin/main.exe -- --test 2>&1|tee t.txt
cd bin;rm t.txt;for x in *.ml;do cat $x >>t.txt;done;cd ..
echo "--" >> bin/t.txt
cat t.txt >> bin/t.txt
echo "--" >> bin/t.txt
echo "输出 patch 即可。Answer in English." >> bin/t.txt
