dir="./build"

if [ ! -d "$dir" ];then
mkdir $dir
fi

if [ -f "CMakeLists.txt" ];then
rm "CMakeLists.txt"
fi

if [ "$1" = "wsl" ]; then 
cp "CMakeLists_wsl.txt" "CMakeLists.txt"
else 
cp "CMakeLists_cygwin.txt" "CMakeLists.txt"
fi

sed -i 's/\r//g' CONFIGURE

line_number=20

cat CONFIGURE | while read line
do 
    if [ -z "$line" ]; then
        continue
    fi
    sed "${line_number}a SET(${line%=*} ${line#*=})" -i CMakeLists.txt
    line_number=$((line_number+1))
done

cd build
if [ "$1" = "windows" ]; then
cmake -G "MinGW_Makefiles" ..
else 
cmake ..
fi
make -j4
