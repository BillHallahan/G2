# Get commits in feature-branch that are not in main
commits=$(git log master..type_refactor --pretty=format:%H)

# Revert them in reverse order (oldest to newest to minimize conflicts)
for sha in $(echo "$commits" | tac); do
    git revert --no-commit "$sha"
done

# Commit the combined revert
git commit -m "Revert commits from type_refactor"