# Maybe we can make this git independent or safer?
# Upgrade redundancies likely exist. Shortcuts are purposefully avoided.

# Vars
FILE="$(realpath -s "$0")"
DIR="$(dirname $FILE)"
PKGDIR="$(dirname $DIR)"


cd "$DIR" 

# Update main package
echo "Updating Auto-Sandbox package."
echo "Currently updating 'production' branch."
git checkout production
git pull -q origin production 

echo "Now updating dependencies."


# TameGenus update
if [ -f "$PKGDIR/MatrixAlgebras/update.sh" ]
then
    sh "$PKGDIR/MatrixAlgebras/update.sh"
else
    echo "Could not find MatrixAlgebras, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/galois60/MatrixAlgebras
    echo "Installing MatrixAlgebras..."
    sh "$PKGDIR/MatrixAlgebras/install.sh"
fi


# TameGenus update
if [ -f "$PKGDIR/TameGenus/update.sh" ]
then
    sh "$PKGDIR/TameGenus/update.sh"
else
    echo "Could not find TameGenus, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/TameGenus
    echo "Installing TameGenus..."
    sh "$PKGDIR/TameGenus/install.sh"
fi


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

# Sylver update
if [ -f "$PKGDIR/Sylver/update.sh" ]
then
    sh "$PKGDIR/Sylver/update.sh"
else
    echo "Could not find Sylver, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Sylver
    echo "Installing Sylver..."
    sh "$PKGDIR/Sylver/install.sh"
fi

# StarAlge update
if [ -f "$PKGDIR/StarAlge/update.sh" ]
then
    sh "$PKGDIR/StarAlge/update.sh"
else
    echo "Could not find StarAlge, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/StarAlge
    echo "Installing StarAlge..."
    sh "$PKGDIR/StarAlge/install.sh"
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

