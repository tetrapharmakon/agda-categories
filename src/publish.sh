agda --html --html-highlight=code $1.lagda.md
pandoc html/$1.md -o $1.html
cp simple.html ~/tetrapharmakon.github.io/_includes/html/
cp $1.lagda.md ~/tetrapharmakon.github.io/stuff/