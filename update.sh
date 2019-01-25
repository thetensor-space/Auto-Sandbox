# Maybe we can make this git independent or safer?
# Upgrade redundancies likely exist. Shortcuts are purposefully avoided.

# Vars
FILE="$(realpath -s "$0")"
DIR="$(dirname $FILE)"
PKGDIR="$(dirname $DIR)"


cd "$DIR" 

# Update main package
echo "Updating Automorphism package."
git pull -q origin master 

echo "Now updating dependencies."



# Filters update
if [ -f "$PKGDIR/Filters/update.sh" ]
then
    sh "$PKGDIR/Filters/update.sh"
else
    echo "Could not find Filters, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/joshmaglione/Filters
    echo "Installing Filters..."
    sh "$PKGDIR/Filters/install.sh"
fi

# Homotopism update
if [ -f "$PKGDIR/Homotopism/update.sh" ]
then
    sh "$PKGDIR/Homotopism/update.sh"
else
    echo "Could not find Homotopism, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Homotopism
    echo "Installing Homotopism..."
    sh "$PKGDIR/Homotopism/install.sh"
fi

# Densor update
if [ -f "$PKGDIR/Densor/update.sh" ]
then
    sh "$PKGDIR/Densor/update.sh"
else
    echo "Could not find Densor, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Densor
    echo "Installing Densor..."
    sh "$PKGDIR/Densor/install.sh"
fi

# CSS update
if [ -f "$PKGDIR/CSS/update.sh" ]
then
    sh "$PKGDIR/CSS/update.sh"
else
    echo "Could not find CSS, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/CSS
    echo "Installing CSS..."
    sh "$PKGDIR/CSS/install.sh"
fi

# TensorSpace update
if [ -f "$PKGDIR/TensorSpace/update.sh" ]
then
    sh "$PKGDIR/TensorSpace/update.sh"
else
    echo "Could not find TensorSpace, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/TensorSpace
    echo "Installing TensorSpace..."
    sh "$PKGDIR/TensorSpace/install.sh"
fi

echo "Successfully updated!"

