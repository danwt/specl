#!/bin/bash
# Install expert-specl skill for Claude Code
set -e

SKILL_NAME="expert-specl"
SKILLS_DIR="$HOME/.claude/skills/$SKILL_NAME"

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo "Installing $SKILL_NAME skill for Claude Code..."

# Check if skill already exists
if [ -d "$SKILLS_DIR" ] || [ -L "$SKILLS_DIR" ]; then
    echo -e "${YELLOW}Warning: $SKILL_NAME skill already exists at $SKILLS_DIR${NC}"
    echo "Remove it first with: rm -rf $SKILLS_DIR"
    exit 1
fi

# Create parent directory if needed
mkdir -p "$HOME/.claude/skills"

# Method 1: Symlink from local clone (auto-updates with git pull)
if [ -d ".claude/skills/$SKILL_NAME" ]; then
    SKILL_PATH="$(cd .claude/skills/$SKILL_NAME && pwd)"
    ln -s "$SKILL_PATH" "$SKILLS_DIR"
    echo -e "${GREEN}✓ Symlinked skill from local repo${NC}"
    echo "  Source: $SKILL_PATH"
    echo "  Target: $SKILLS_DIR"
    echo -e "\n${GREEN}The skill will auto-update when you 'git pull' this repo${NC}"

# Method 2: Extract from .skill archive (static copy)
elif [ -f "$SKILL_NAME.skill" ]; then
    unzip -q "$SKILL_NAME.skill" -d "$HOME/.claude/skills"
    echo -e "${GREEN}✓ Installed skill from archive${NC}"
    echo "  Location: $SKILLS_DIR"
    echo -e "\n${YELLOW}Note: This is a static copy. To get updates, re-run this script.${NC}"

else
    echo -e "${RED}Error: Could not find skill files${NC}"
    echo "Run this script from the specl repo root directory."
    echo "Expected to find either:"
    echo "  - .claude/skills/$SKILL_NAME/ (directory)"
    echo "  - $SKILL_NAME.skill (archive)"
    exit 1
fi

echo -e "\n${GREEN}Installation complete!${NC}"
echo "You can now use /${SKILL_NAME} in Claude Code"
echo ""
echo "Examples:"
echo "  - Let Claude auto-detect: 'Help me model a distributed consensus protocol'"
echo "  - Invoke directly: '/expert-specl help me debug this invariant violation'"
