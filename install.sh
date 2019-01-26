# Vars
FILE="$(realpath -s "$0")"              # Full path to this file
DIR="$(dirname $FILE)"                  # Current directory
PKGDIR="$(dirname $DIR)"                # Directory for dependencies
START="${HOME}/.magmarc"                # Magma start file location

# Dependencies and .spec locations
ATTACH1="AttachSpec(\"$PKGDIR/TensorSpace/TensorSpace.spec\");"
ATTACH2="AttachSpec(\"$PKGDIR/StarAlge/StarAlge.spec\");"
ATTACH3="AttachSpec(\"$PKGDIR/Homotopism/Homotopism.spec\");"
ATTACH4="AttachSpec(\"$PKGDIR/CSS/CSS.spec\");"
ATTACH5="AttachSpec(\"$PKGDIR/Densor/Densor.spec\");"
ATTACH6="AttachSpec(\"$PKGDIR/Filters/Filters.spec\");"
ATTACH7="AttachSpec(\"$DIR/Automorphism.spec\");"
# MORE SOON



echo "Automorphism.spec is in $DIR"


echo "Dependencies will be downloaded to $PKGDIR"




# Filters install/ update
if [ -f "$PKGDIR/Filters/update.sh" ]
then
    echo "Filters already installed, updating..."
    sh "$PKGDIR/Filters/update.sh"
else
    echo "Could not find Filters, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/joshmaglione/Filters
fi


# Homotopism install/ update
if [ -f "$PKGDIR/Homotopism/update.sh" ]
then
    echo "Homotopism already installed, updating..."
    sh "$PKGDIR/Homotopism/update.sh"
else
    echo "Could not find Homotopism, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Homotopism
fi


# Densor install/ update
if [ -f "$PKGDIR/Densor/update.sh" ]
then
    echo "Densor already installed, updating..."
    sh "$PKGDIR/Densor/update.sh"
else
    echo "Could not find Densor, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Densor
fi


# CSS install/ update
if [ -f "$PKGDIR/CSS/update.sh" ]
then
    echo "CSS already installed, updating..."
    sh "$PKGDIR/CSS/update.sh"
else
    echo "Could not find CSS, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/CSS
fi


# StarAlge install/ update
if [ -f "$PKGDIR/StarAlge/update.sh" ]
then
    echo "StarAlge already installed, updating..."
    sh "$PKGDIR/StarAlge/update.sh"
else
    echo "Could not find StarAlge, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/StarAlge
fi


# TensorSpace install/ update
if [ -f "$PKGDIR/TensorSpace/update.sh" ]
then
    echo "TensorSpace already installed, updating..."
    sh "$PKGDIR/TensorSpace/update.sh"
else
    echo "Could not find TensorSpace, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/TensorSpace
fi

echo "Dependencies downloaded."




# Construct Magma start file

if [ -f "$START" ]
then
    echo "Found a Magma start file"
    for A in "$ATTACH1" "$ATTACH2" "$ATTACH3" "$ATTACH4" "$ATTACH5" "$ATTACH6"\
        "$ATTACH7"
    do
        if grep -Fxq "$A" "$START"
        then
            echo "Already installed"
        else
            echo "$A" >> "$START"
        fi
    done
else
    echo "Creating a Magma start file: $START"
    echo "// Created by an install file for Magma start up." > "$START"
    for A in "$ATTACH1" "$ATTACH2" "$ATTACH3" "$ATTACH4" "$ATTACH5" "$ATTACH6"\
        "$ATTACH7"
    do
        echo "$A" >> "$START"
    done
fi

echo "Successfully installed"

