# Vars
FILE="$(realpath -s "$0")"              # Full path to this file
DIR="$(dirname $FILE)"                  # Current directory
PKGDIR="$(dirname $DIR)"                # Directory for dependencies
START="${HOME}/.magmarc"                # Magma start file location

# Dependencies and .spec locations
ATTACH1="AttachSpec(\"$PKGDIR/TensorSpace/TensorSpace.spec\");"
ATTACH2="AttachSpec(\"$PKGDIR/StarAlge/StarAlge.spec\");"
ATTACH3="AttachSpec(\"$PKGDIR/Homotopism/Homotopism.spec\");"
ATTACH4="AttachSpec(\"$PKGDIR/Sylver/Sylver.spec\");"
ATTACH5="AttachSpec(\"$PKGDIR/Densor/Densor.spec\");"
ATTACH6="AttachSpec(\"$PKGDIR/Filters/Filters.spec\");"
ATTACH7="AttachSpec(\"$PKGDIR/MatrixAlgebras/MatrixAlgebras.spec\");"
ATTACH8="AttachSpec(\"$PKGDIR/TameGenus/TameGenus.spec\");"
ATTACH9="AttachSpec(\"$DIR/Auto-Sandbox.spec\");"



echo "Auto-Sandbox.spec is in $DIR"


echo "Dependencies will be downloaded to $PKGDIR"



# TameGenus install/ update
if [ -f "$PKGDIR/TameGenus/update.sh" ]
then
    echo "TameGenus already installed, updating..."
    sh "$PKGDIR/TameGenus/update.sh"
else
    echo "Could not find TameGenus, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/TameGenus
fi


# MatrixAlgebras install/ update
if [ -f "$PKGDIR/MatrixAlgebras/update.sh" ]
then
    echo "MatrixAlgebras already installed, updating..."
    sh "$PKGDIR/MatrixAlgebras/update.sh"
else
    echo "Could not find MatrixAlgebras, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/galois60/MatrixAlgebras
fi


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


# Sylver install/ update
if [ -f "$PKGDIR/Sylver/update.sh" ]
then
    echo "Sylver already installed, updating..."
    sh "$PKGDIR/Sylver/update.sh"
else
    echo "Could not find Sylver, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Sylver
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
        "$ATTACH7" "$ATTACH8" "$ATTACH9"
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
        "$ATTACH7" "$ATTACH8" "$ATTACH9"
    do
        echo "$A" >> "$START"
    done
fi

echo "Successfully installed"

